"""Serialized participant policy over immutable historical model objects.

IDs stand for authenticated hash identities; races are already weighted and
totally ordered. This idealization assumes healthy recovered storage, available
execution and timer service. Cryptography, transaction demand, buffer capacity,
authority rotation and slashing are outside this model.

Historical envelopes and the canonical proposal endorsement index are separate.
Only owner tasks emit honest messages. Every receiver normalizes the same live
inventory; a validator additionally filters targets through its next Vote.
"""
from dataclasses import dataclass, replace
import consensus as consensus_model
from consensus import (
    Evidence,
    ModelError,
    Validator,
    Vote,
    actionable,
    advance_coverage,
    best_endorseable,
    best_model_candidate,
    build_proposal,
    candidate_selectable,
    check_vote_reset,
    check_vote_slot,
    direct_conflict,
    evidence_source,
    fork_order,
    proposal_improves,
    prospective_vote,
    require,
    require_finalized_lineage,
    retain_evidence_only,
    stage_block,
    submit_vote,
    validate_evidence_vote,
    validate_vote_authentication,
    validate_vote_position,
    view_evidence,
)


def vote_body(vote):
    """HashSignedVote hashes semantic content, not a fresh outer signature ID.

    The symbolic inner_id already represents HashVoteIdentity. See types/vote.go:141.
    """
    return vote.inner_id, vote.target, vote.stake, vote.prev_self, vote.exclusions


def check_vote_identity(vote, known):
    for old in known:
        require(old.id != vote.id or old == vote, 'Vote identity collision')
        require(vote_body(old) != vote_body(vote) or old.id == vote.id,
                'same signed Vote body has different symbolic identities')


@dataclass(frozen=True)
class PreparedProposal:
    parent: int
    own_vote: Vote
    endorsements: tuple[Vote, ...]
    historical: bool = False


class Node:
    """One serialized owner plus its ingress buffer and durable signing state.

    The wrapper is mutable so a durable emission/reservation survives a later
    owner-admission failure. Its historical Validator snapshots stay immutable.
    """
    def __init__(self, genesis, identity, recovered=True):
        self.state = (Validator.observer(genesis) if identity is None
                      else Validator.init(genesis, identity))
        self.endorsements = {}
        self.live_votes = set()
        self.durable = []
        self.claimed_heights, self.claimed_positions = set(), set()
        self.proposed_heights = set()
        self.pending = {}
        self._retrying = False
        self.publications = []
        self.recovered = recovered
        self.signing_error = None

    def proposal_votes(self, target):
        return tuple(vote for (block, _), vote in sorted(self.endorsements.items())
                     if block == target)

    def _check_index(self, vote):
        old = self.endorsements.get((vote.target, vote.signer))
        require(old is None or old == vote, 'conflicting endorsement')

    def _index(self, vote):
        key = vote.target, vote.signer
        old = self.endorsements.get(key)
        if old is None:
            self.endorsements[key] = vote

    def _select(self, state):
        # model_selection.go uses the installed owner checkpoint's exact path.
        # Lifetime emissions can include a durable signature rejected by owner
        # admission; those signatures must not become selection checkpoints.
        try:
            view = replace(state, emitted=tuple(state.self_branch(state.latest)))
            candidate = best_endorseable(view)
            if candidate is None:
                return state
            selected = advance_coverage(view, candidate)
        except ModelError:
            # autoCheckFinalityFromTip leaves successful admission intact when
            # local selection is unavailable or ineligible.
            return state
        return replace(selected, emitted=state.emitted)

    def _live_replay(self, vote):
        return vote in self.live_votes and (
            self.endorsements.get((vote.target, vote.signer)) == vote
            or not any(b.id == vote.target for b in self.state.blocks)
            or not actionable(self.state, vote.target))

    # Ingress and evidence retention. These methods never sign and never append
    # to the durable local emission log.
    def admit_index_component(self, vote):
        """ConsensusState index boundary; Engine history validation is separate.

        This is exposed for native component correspondence, not wire ingress.
        Symbolic envelopes represent successfully verified signatures.
        """
        target = self.state.block(vote.target)
        require_finalized_lineage(self.state, target.id)
        validate_vote_position(target, vote)
        check_vote_slot(self.state, vote)
        self._check_index(vote)
        replay = (vote.target, vote.signer) in self.endorsements
        self._index(vote)
        return 'replay' if replay else 'accepted'

    def _precheck_unknown_target_vote(self, vote):
        """Mirror InboundBuffer's current-finalized-authority admission gate.

        Symbolic Vote values stand for envelopes whose signature and VRF proof
        have already verified. The remaining checks are available before the
        target block arrives.
        """
        finalized = self.state.block(self.state.finalized)
        require(vote.height > 0, 'vote height is zero')
        require(vote.height - 1 >= finalized.height,
                'vote target is below finalized height')
        require(vote.chain == finalized.state.chain, 'wrong chain')
        stake = finalized.state.stake(vote.signer)
        require(stake > 0 and vote.stake == stake, 'wrong stake')

    def _buffer(self, key, args):
        old = self.pending.get(key)
        require(old is None or old == args, 'pending identity collision')
        self.pending[key] = args
        return 'buffered'

    def _retain_direct_conflict_evidence(self, vote, *, blocks=(), votes=()):
        """Keep a rejected authenticated action outside live consensus.

        This evidence-only owner path intentionally diverges from current Go.
        The authenticated checkpoint, resolver isolation and persistence rules
        still require a Go port.
        """
        # Authenticate against the staged closure before the rejected action
        # itself is eligible to resolve any proof. Block/direction conflicts
        # are evidence; malformed Vote context is not.
        context = retain_evidence_only(
            self.state, blocks=blocks, votes=votes)
        validate_vote_authentication(
            context, vote, allow_evidence_target=True)
        # Preserve every independently verified portable proof carried by the
        # rejected envelope.  Side Votes are deliberately not scanned as live
        # accountability history, so dropping these top-level references here
        # would make valid evidence disappear from the actionable view.  Block
        # records were authenticated by stage_block; retain_evidence_only
        # verifies them again against the disjoint resolver before publishing.
        carried = (*vote.exclusions,
                   *(record.proof for block in blocks
                     for record in block.exclusions))
        retained = retain_evidence_only(
            context, votes=(vote,), proofs=carried)
        source = evidence_source(retained)
        conflict = None
        # Prefer the exact occupied Block: it is the narrowest proof of the
        # rejected action. Fall back deterministically to any other
        # direct conflict on the signer's authenticated self history.
        block_key = vote.signer, vote.chain, vote.target
        for previous in sorted(source.votes, key=lambda item: (
                (item.signer, item.chain, item.target) != block_key, item.id)):
            if previous.id == vote.id:
                continue
            try:
                if direct_conflict(source, previous, vote):
                    conflict = previous
                    break
            except ModelError as error:
                if error.kind not in ('missing_vote', 'missing_block'):
                    raise
        if conflict is None:
            return False
        proof = Evidence(vote.signer,
                         tuple(sorted((conflict.id, vote.id))))
        self.state = retain_evidence_only(retained, proofs=(proof,))
        return True

    def _handle_rejected_conflict(self, key, args, vote, *, blocks=(), votes=()):
        """Retain a proved conflict, or buffer an unavailable auth closure."""
        try:
            retained = self._retain_direct_conflict_evidence(
                vote, blocks=blocks, votes=votes)
        except ModelError as error:
            if error.kind in ('missing_vote', 'missing_block'):
                return self._buffer(key, args)
            raise
        if not retained:
            return None
        self.pending.pop(key, None)
        self.retry_pending()
        return 'retained'

    def _retain_embedded_conflicts(self, block):
        """Keep independently authenticated conflicts from a rejected Block.

        A malformed Block cannot make its batch live, but it also cannot wash
        a valid signed conflict carried in that batch.  Current Go lacks this
        retention seam and still needs a port of its resolver isolation.
        """
        changed = False
        for vote in block.endorsements:
            try:
                changed |= self._retain_direct_conflict_evidence(vote)
            except ModelError as error:
                # The containing admission error remains authoritative.  An
                # authenticated-but-unavailable Vote is repaired independently;
                # a malformed embedded Vote is not partial proof.
                if error.kind in ('missing_vote', 'missing_block'):
                    self._buffer(('vote', vote.id), (vote,))
                continue
        if changed:
            self.retry_pending()
        return changed

    def _receive_evidence_proposal(self, key, block, own):
        """Authenticate historical ancestry before considering a valid child.

        A clean descendant can activate its required Block path. Conflicting
        parent Votes stay evidence-only and never enter the endorsement index.
        Current Go needs this resolver and admission split before porting.
        """
        # Treat the disjoint closure as historical input only long enough to
        # apply ordinary Block and detached-Vote validity rules. Only the
        # authenticated ancestry needed by an eligible child may activate.
        try:
            staged = stage_block(evidence_source(self.state), block)
            validate_vote_authentication(staged, own)
        except ModelError as exc:
            if exc.kind in ('missing_block', 'missing_vote'):
                return self._buffer(key, (block, own))
            self._retain_embedded_conflicts(block)
            raise
        activate = actionable(staged, block.id)
        try:
            if activate:
                check_vote_reset(staged, own)
            submit_vote(staged, own)
        except ModelError as exc:
            if exc.kind in ('missing_block', 'missing_vote'):
                return self._buffer(key, (block, own))
            if self._handle_rejected_conflict(
                    key, (block, own), own,
                    blocks=(block,), votes=block.endorsements) == 'buffered':
                return 'buffered'
            raise

        carried = (*own.exclusions,
                   *(record.proof for record in block.exclusions))
        if activate:
            self._check_index(own)
            context = retain_evidence_only(
                self.state, votes=block.endorsements, proofs=carried)
            live = {item.id for item in context.blocks}
            dependencies = tuple(item for item in staged.ancestry(block.id)
                                 if item.id not in live)
            activated = {item.id for item in dependencies}
            context = replace(
                context, blocks=dependencies + context.blocks,
                evidence_blocks=tuple(item for item in context.evidence_blocks
                                      if item.id not in activated),
                evidence_votes=tuple(item for item in context.evidence_votes
                                     if item.id != own.id))
            admitted = submit_vote(context, own)
            self._index(own)
            self.live_votes.add(own)
            self.state = self._select(admitted) if self.recovered else admitted
            self.pending.pop(key, None)
            self.retry_pending()
            return 'accepted'
        self.state = retain_evidence_only(
            self.state, blocks=(block,),
            votes=(*block.endorsements, own), proofs=carried)
        self.pending.pop(key, None)
        self.retry_pending()
        return 'evidence'

    def receive_vote(self, vote):
        """Retain an authenticated unknown-target vote and recheck it locally."""
        key = ('vote', vote.id)
        check_vote_identity(vote, (*self.state.votes, *self.state.evidence_votes))
        if vote in self.state.evidence_votes:
            self.pending.pop(key, None)
            return 'evidence'
        if self._live_replay(vote):
            self.pending.pop(key, None)
            return 'replay'
        if not any(b.id == vote.target for b in self.state.blocks):
            if any(b.id == vote.target for b in self.state.evidence_blocks):
                # The target was authenticated while staging a rejected
                # conflict.  Validate this dependency through the side resolver
                # and retain it there; it must never become live stake or a tip.
                try:
                    validate_evidence_vote(self.state, vote)
                except ModelError as exc:
                    if exc.kind in ('missing_vote', 'missing_block'):
                        return self._buffer(key, (vote,))
                    if self._handle_rejected_conflict(
                            key, (vote,), vote) == 'buffered':
                        return 'buffered'
                    raise
                self.state = retain_evidence_only(
                    self.state, votes=(vote,), proofs=vote.exclusions)
                self.pending.pop(key, None)
                self.retry_pending()
                return 'evidence'
            self._precheck_unknown_target_vote(vote)
            return self._buffer(key, (vote,))
        try:
            validate_vote_authentication(self.state, vote)
        except ModelError as exc:
            if exc.kind in ('missing_vote', 'missing_block'):
                return self._buffer(key, (vote,))
            raise
        try:
            check_vote_slot(self.state, vote)
            self._check_index(vote)
            require_finalized_lineage(self.state, vote.target)
            check_vote_reset(self.state, vote)
            staged = submit_vote(self.state, vote)
        except ModelError as exc:
            if exc.kind in ('missing_vote', 'missing_block'):
                return self._buffer(key, (vote,))
            if self._handle_rejected_conflict(
                    key, (vote,), vote) == 'buffered':
                return 'buffered'
            raise
        self.state = staged
        self.live_votes.add(vote)
        self._index(vote)
        self.pending.pop(key, None)
        self.retry_pending()
        return 'accepted'

    def receive_proposal(self, block, own):
        key = ('proposal', block.id, own.id)
        require(own.target == block.id and own.signer == block.proposer,
                'detached self-vote does not bind candidate and proposer')
        for vote in (*block.endorsements, own):
            check_vote_identity(vote, (*self.state.votes,
                                       *self.state.evidence_votes))
        old = next((b for b in self.state.blocks if b.id == block.id), None)
        side = next((b for b in self.state.evidence_blocks if b.id == block.id), None)
        require(side is None or side == block, 'Block identity collision')
        if old is not None:
            require(old == block, 'Block identity collision')
            # engine.go:1889/2069: an exact remote replay does not select again.
            if (own in self.live_votes and own in self.state.votes
                    and self.endorsements.get((own.target, own.signer)) == own):
                self.pending.pop(key, None)
                return 'replay'
            try:
                validate_vote_authentication(self.state, own)
            except ModelError as exc:
                if exc.kind in ('missing_vote', 'missing_block'):
                    return self._buffer(key, (block, own))
                raise
            try:
                self._check_index(own)
                submit_vote(self.state, own)
            except ModelError:
                if self._handle_rejected_conflict(
                        key, (block, own), own) == 'buffered':
                    return 'buffered'
                raise
            if self._handle_rejected_conflict(
                    key, (block, own), own) == 'buffered':
                return 'buffered'
            raise ModelError('duplicate block with unaccepted self-vote')
        if (side is not None or
                (block.parent is not None and any(
                    parent.id == block.parent
                    for parent in self.state.evidence_blocks)) or any(
                    parent.id == block.parent and not actionable(self.state, parent.id)
                    for parent in self.state.blocks)):
            return self._receive_evidence_proposal(key, block, own)
        try:
            staged = stage_block(self.state, block)
            if not actionable(staged, block.id):
                # A compatible historical action may name a predecessor on this
                # retired fork. Authenticate it without making the
                # fork live support or moving the installed finalized path.
                return self._receive_evidence_proposal(key, block, own)
            require_finalized_lineage(staged, block.id)
        except ModelError as exc:
            if exc.kind in ('missing_block', 'missing_vote'):
                return self._buffer(key, (block, own))
            self._retain_embedded_conflicts(block)
            raise
        try:
            validate_vote_authentication(staged, own)
        except ModelError as exc:
            if exc.kind in ('missing_block', 'missing_vote'):
                return self._buffer(key, (block, own))
            raise
        try:
            self._check_index(own)
            check_vote_reset(staged, own)
            staged = submit_vote(staged, own)
        except ModelError as exc:
            if exc.kind in ('missing_block', 'missing_vote'):
                return self._buffer(key, (block, own))
            # The Block has passed admission independently of its detached
            # self-vote. Keep it live for ordinary fork ranking, while a
            # conflicting detached Vote remains evidence-only and supplies no
            # quorum support.
            previous = self.state
            self.state = staged
            retained = self._handle_rejected_conflict(key, (block, own), own)
            if retained == 'buffered':
                self.state = previous
                return 'buffered'
            if retained != 'retained':
                self.state = previous
                raise
            for vote in block.endorsements:
                self._index(vote)
                self.live_votes.add(vote)
            self.state = self._select(self.state) if self.recovered else self.state
            self.pending.pop(key, None)
            self.retry_pending()
            return 'accepted'
        # Carried historical bodies remain distinct from the canonical index.
        for vote in block.endorsements:
            self._index(vote)
            self.live_votes.add(vote)
        self._index(own)
        self.live_votes.add(own)
        self.state = self._select(staged) if self.recovered and old is None else staged
        self.pending.pop(key, None)
        self.retry_pending()
        return 'accepted'

    def retry_pending(self):
        if self._retrying:
            return
        self._retrying = True
        try:
            while self.pending:
                before = self.state
                for key, args in tuple(self.pending.items()):
                    try:
                        if key[0] == 'vote':
                            self.receive_vote(*args)
                        else:
                            self.receive_proposal(*args)
                    except ModelError:
                        self.pending.pop(key, None)
                if self.state == before:
                    break
        finally:
            self._retrying = False

    # Local signing and proposal scheduling. Preparation may publish a parent
    # vote; commit owns reservation, child signing, admission, and publication.
    def _current(self, expected=None):
        require(self.signing_error is None, 'local signing disabled after owner rejection')
        target = best_endorseable(self.state)
        require(target is not None, 'no current best candidate')
        require(expected is None or target == expected, 'requested target is not current best')
        return target

    def _proposal_choice(self, expected=None):
        """Choose the ordinary best endorseable parent."""
        require(self.signing_error is None,
                'local signing disabled after owner rejection')
        parent = best_endorseable(self.state)
        require(parent is not None, 'no current best proposal parent')
        require(expected is None or parent == expected,
                'requested target is not current best')
        return parent, None

    def proposal_parent(self):
        """Read-only parent query used by the ordinary proposal scheduler."""
        try:
            return self._proposal_choice()[0]
        except ModelError:
            return None

    def _sign(self, v, target, identity, race, sig_hash):
        require(v.identity is not None, 'observer cannot sign')
        require(self.recovered, 'local signing recovery is incomplete')
        require_finalized_lineage(v, target)
        if self.durable:
            head = self.durable[-1]
            block = v.block(target)
            position = (v.identity, block.state.chain, block.height + 1, block.proposer,
                        block.proposer_vote.inner_id if block.proposer_vote else None)
            if head.inner == position and head.target == target:
                # Exact retained head, not a freshly signed same-target retry.
                # Owner may have rejected the earlier emission after it was
                # durably signed. Revalidate that exact body; never sign another.
                submit_vote(v, head)
                return head
        # The private chronological emission log survives Q3 segment resets.
        # Prospective signing uses it, not the set of received self envelopes.
        latest = self.durable[-1].id if self.durable else None
        signing = replace(v, latest=latest)
        vote = prospective_vote(signing, target, identity, race, sig_hash)
        old = next((old for old in v.votes if old.inner == vote.inner), None)
        if old is not None:
            require((old.race, old.sig_hash) == (race, sig_hash), 'inner signing material changed')
            vote = replace(vote, inner_id=old.inner_id)
        require(v.identity not in {e.offender for e in vote.exclusions}, 'excluded local signer')
        # A received exact body already determines the native complete hash.
        same = next((old for old in v.votes if vote_body(old) == vote_body(vote)), None)
        if same is not None:
            vote = replace(vote, id=same.id)
        require(all(old.id != vote.id for old in self.durable),
                'durable Vote identity already used')
        check_vote_slot(v, vote)
        submit_vote(v, vote)  # PrepareLocalModelVoteForSigning before persistence.
        self.durable.append(vote)
        # Persistence precedes owner admission: even a later rejection cannot
        # erase this emission or turn the next signature into a fresh root.
        self.state = replace(self.state, emitted=tuple(reversed(self.durable)))
        return vote

    def endorse_current_best(self, identity, race, sig_hash, expected=None):
        target = self._current(expected)
        vote = self._sign(self.state, target, identity, race, sig_hash)
        try:
            if not self._live_replay(vote):
                self._check_index(vote)
            admitted = submit_vote(self.state, vote)
        except ModelError as exc:
            # participant.go:1670: rejection after a durable signature disables
            # later local signing; a private pre-sign refusal above does not.
            self.signing_error = str(exc)
            raise
        self._index(vote)
        self.live_votes.add(vote)
        # engine.go:1546: owner latest is installed before selection/finality.
        self.state = self._select(replace(admitted, latest=vote.id))
        self.publications.append(('vote', vote))
        self.retry_pending()
        return vote

    def prepare_proposal(self, vote_id, race, sig_hash, expected=None):
        parent_id, historical = self._proposal_choice(expected)
        parent = self.state.block(parent_id)
        require(parent.height + 1 not in self.proposed_heights, 'proposal height already proposed')
        # Driver successes suppress before endorsement; a failed durable intent
        # is checked only at commit, after another parent-vote publication.
        position = parent.proposer_vote.inner_id if parent.proposer_vote else None
        require(position not in self.claimed_positions, 'proposal position already proposed')
        snapshot = self.proposal_votes(parent_id)
        own = (historical if historical is not None else
               self.endorse_current_best(vote_id, race, sig_hash,
                                         expected=parent_id))
        votes = {vote.signer: vote for vote in snapshot}
        votes[self.state.identity] = own
        votes = tuple(votes[who] for who in sorted(votes))
        authority = parent.state
        if not authority.admits(sum(authority.stake(vote.signer) for vote in votes)):
            return None
        return PreparedProposal(parent_id, own, votes, historical is not None)

    def same_height_outranks(self, candidate):
        staged = replace(self.state, blocks=(candidate,) + self.state.blocks)
        return any(b.height == candidate.height and actionable(self.state, b.id) and
                   candidate_selectable(self.state, b.id) and
                   fork_order(self.state, b, candidate, unsigned=candidate.id) < 0 and
                   not proposal_improves(staged, candidate.id, b.id)
                   for b in self.state.blocks)

    def commit_proposal(self, prepared, block_id, own_id, race, sig_hash,
                        fail_after_reservation=False):
        parent_id, historical = self._proposal_choice(prepared.parent)
        require(parent_id == prepared.parent and
                ((historical == prepared.own_vote) if prepared.historical
                 else historical is None),
                'prepared proposal parent is no longer actionable')
        v = self.state
        parent = v.block(prepared.parent)
        height = parent.height + 1
        require(height not in self.claimed_heights, 'proposal height already reserved')
        require(prepared.own_vote.prev_vote not in self.claimed_positions, 'proposal position already reserved')
        require(not any(b.id == block_id for b in v.blocks), 'Block identity already used')
        b = build_proposal(v, parent.id, prepared.own_vote,
                           prepared.endorsements, block_id)
        require(not self.same_height_outranks(b), 'existing same-height block outranks proposal')
        staged = stage_block(v, b)  # Includes strict parent Q1/pending-stake progress.
        self.claimed_heights.add(height)
        require(not fail_after_reservation, 'injected build failure after reservation')
        own = self._sign(staged, b.id, own_id, race, sig_hash)
        self._check_index(own)
        staged = submit_vote(staged, own)
        for vote in b.endorsements:
            self._index(vote)
            self.live_votes.add(vote)
        self._index(own)
        self.live_votes.add(own)
        self.state = self._select(replace(staged, latest=own.id,
                                         emitted=tuple(reversed(self.durable))))
        self.claimed_positions.add(prepared.own_vote.prev_vote)
        self.proposed_heights.add(height)
        self.publications.append(('proposal', b, own))
        self.retry_pending()
        return b, own
