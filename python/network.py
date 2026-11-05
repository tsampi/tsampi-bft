"""Atomic owner/network transitions for the symbolic consensus model.

Call ``Network.step(action)`` with an explicit action; it returns ``None`` or
the refusal reason. A requested honest target is a current-best assertion, not
permission to bypass owner candidate selection. Publication is not delivery.
Byzantine publication actions may supply arbitrary own objects but cannot forge
an honest Vote. Honest receiver state changes only through these transitions.

Delivery order belongs to ``event_delivery.py``. This module has no rounds,
partition switch, message replay sweep, or randomized scheduler. Fixed symbolic
identities and race values are deterministic test values, not cryptography.
"""

from consensus import Block, ModelError, State, Validator, has_quorum, require
from owner import Node, best_endorseable, check_vote_identity


DEFAULT_ENDORSE_THRESHOLD = (2, 3)


class Network:
    def __init__(self, honest_stakes=(1, 1, 1), byzantine_stake=1,
                 max_block_height=128, trace=False,
                 threshold=DEFAULT_ENDORSE_THRESHOLD):
        require(max_block_height > 0, 'invalid simulation bounds')
        require(honest_stakes and all(s > 0 for s in honest_stakes) and byzantine_stake > 0,
                'all validator Stakes must be positive')
        members = tuple(enumerate((*honest_stakes, byzantine_stake)))
        self.genesis = Block.genesis(0, State(1, members, *threshold))
        self.honest = tuple(range(len(honest_stakes)))
        require(has_quorum(self.genesis.state, self.honest), 'insufficient honest Stake')
        self.receivers = {i: Validator.init(self.genesis, i) for i in self.honest}
        self.owners = {i: Node(self.genesis, i) for i in self.honest}
        self.last_delivery_status = None
        self.blocks = {0: self.genesis}
        self.votes = {}
        self.proposals = {}  # (Block ID, detached Vote ID) -> exact envelope
        self.actions = []
        self.transitions = []
        self.paths = {(0,)}
        self.agreement = True
        self.fresh = 1
        self.max_block_height, self.trace = max_block_height, trace

    def alloc(self):
        require(self.fresh < 2**32, 'symbolic identity space exhausted')
        id = self.fresh
        self.fresh += 1
        return id

    def rank(self, who):
        return 1 + who

    def signing_material(self, who, target):
        v = self.receivers[who]
        b = v.block(target)
        inner = (who, b.state.chain, b.height + 1, b.proposer,
                 b.proposer_vote.inner_id if b.proposer_vote else None)
        old = next((vote for vote in v.votes if vote.inner == inner), None)
        return (old.race, old.sig_hash) if old else (self.rank(who), self.rank(who))

    def child_signing_material(self, who, prepared, race, signature):
        return race, signature

    def owner(self, who):
        if who not in self.owners:
            self.owners[who] = Node(self.genesis, who)
        require(self.owners[who].state == self.receivers[who],
                'receiver state was changed outside Go owner operations')
        return self.owners[who]

    def holds_message(self, who, kind, *identity):
        """Available peer inventory; a discarded wire receipt is not a copy."""
        v = self.receivers[who]
        # The evidence-side inventory is a Python model extension.
        # Go must port the same disjoint resolver before relying on this path.
        if kind == 'deliver_proposal':
            b, own = self.proposals[tuple(identity)]
            if ((b in v.blocks and own in v.votes) or
                    (b in v.evidence_blocks and own in v.evidence_votes)):
                return True
            return ('proposal', *identity) in self.owner(who).pending
        vote = self.votes[identity[0]]
        if vote in v.votes or vote in v.evidence_votes:
            return True
        pending = self.owner(who).pending
        return (('vote', vote.id) in pending or any(
            key[0] == 'proposal' and (vote == args[1] or vote in args[0].endorsements)
            for key, args in pending.items()))

    def step(self, action):
        """Atomic Network.apply/attempt; catalog never supplies receiver state.

        sign_vote(who, target, id, race, sig_hash)
        propose(who, parent, block_id, self_id, race, sig_hash)
        publish_vote(vote), publish_proposal(block, self_vote)
        deliver_vote(who, vote_id), deliver_proposal(who, block_id, self_id), idle()
        A height/action ceiling raises RuntimeError, not a protocol refusal.
        """
        if len(self.actions) >= 12000:
            raise RuntimeError('action budget exhausted')
        before_receivers = self.receivers
        receivers, blocks = self.receivers.copy(), self.blocks.copy()
        votes, proposals = self.votes.copy(), self.proposals.copy()

        def register_vote(vote):
            check_vote_identity(vote, votes.values())
            if vote.id in votes:
                require(votes[vote.id] == vote, 'symbolic Vote identity collision')
                return
            for old in votes.values():
                if old.inner == vote.inner:
                    require((old.inner_id, old.race, old.sig_hash) ==
                            (vote.inner_id, vote.race, vote.sig_hash), 'symbolic inner Vote changed')
                else:
                    require(old.inner_id != vote.inner_id, 'symbolic inner identity collision')
            votes[vote.id] = vote

        def objects(b, own):
            return (own,) + ((b.proposer_vote,) if b.proposer_vote else ()) + b.endorsements

        def register_proposal(b, own):
            require(b.id not in blocks or blocks[b.id] == b, 'symbolic Block identity collision')
            blocks[b.id] = b
            for vote in objects(b, own):
                register_vote(vote)
            proposals[b.id, own.id] = (b, own)

        def authenticate(vote):
            require(vote.signer not in self.honest or self.votes.get(vote.id) == vote,
                    'honest Vote was not emitted')

        error = None
        kind, *args = action
        policy_owner = (self.owner(args[0]) if kind in
                        ('sign_vote', 'propose', 'deliver_vote', 'deliver_proposal')
                        and args[0] in self.receivers else None)
        publication_start = len(policy_owner.publications) if policy_owner else 0
        self.last_delivery_status = None
        try:
            if kind in ('sign_vote', 'propose', 'deliver_vote', 'deliver_proposal'):
                require(args[0] in receivers, 'unknown honest receiver')
            if kind == 'sign_vote':
                who, *params = args
                target, identity, race, sig = params
                vote = policy_owner.endorse_current_best(identity, race, sig, expected=target)
                next_v = policy_owner.state
                register_vote(vote)
                receivers[who] = next_v
            elif kind == 'propose':
                who, *params = args
                if receivers[who].block(params[0]).height + 1 > self.max_block_height:
                    raise RuntimeError('Block height ceiling exceeded before generation')
                target, block_id, own_id, race, sig = params
                parent_race, parent_sig = self.signing_material(who, target)
                prepared = policy_owner.prepare_proposal(self.alloc(), parent_race, parent_sig, expected=target)
                require(prepared is not None, 'insufficient endorsement stake')
                race, sig = self.child_signing_material(who, prepared, race, sig)
                b, own = policy_owner.commit_proposal(prepared, block_id, own_id, race, sig)
                next_v = policy_owner.state
                register_proposal(b, own)
                receivers[who] = next_v
            elif kind == 'publish_vote':
                vote, = args
                authenticate(vote)
                register_vote(vote)
            elif kind == 'publish_proposal':
                b, own = args
                if b.height > self.max_block_height:
                    raise RuntimeError('Block height ceiling exceeded before publication')
                for vote in objects(b, own):
                    authenticate(vote)
                register_proposal(b, own)
            elif kind == 'deliver_vote':
                who, id = args
                if id not in votes:
                    raise ModelError(f'missing Vote {id}', 'missing_vote', id)
                self.last_delivery_status = policy_owner.receive_vote(votes[id])
                receivers[who] = policy_owner.state
            elif kind == 'deliver_proposal':
                who, block_id, self_id = args
                require((block_id, self_id) in proposals, 'proposal envelope is unavailable')
                self.last_delivery_status = policy_owner.receive_proposal(*proposals[block_id, self_id])
                receivers[who] = policy_owner.state
            elif kind != 'idle':
                raise ValueError(f'unknown action: {kind}')
        except ModelError as exc:
            error = str(exc)
        if policy_owner:
            # A parent vote accepted before a failed proposal remains emitted;
            # durable reservations are also retained on the owner object.
            receivers[args[0]] = policy_owner.state
            for publication in policy_owner.publications[publication_start:]:
                if publication[0] == 'vote':
                    register_vote(publication[1])
                else:
                    register_proposal(*publication[1:])
        if error is None or policy_owner:
            if max(b.height for b in blocks.values()) > self.max_block_height:
                raise RuntimeError('Block height ceiling exceeded; action not applied')
            for who, v in receivers.items():
                path = tuple(b.id for b in v.ancestry(v.finalized))
                if self.receivers[who].finalized not in path:
                    raise RuntimeError('finalized lineage regressed')
                if v.finalized not in (b.id for b in v.ancestry(v.tip)):
                    raise RuntimeError('finalized is outside selected tip ancestry')
                self.agreement &= all(path[:len(old)] == old or old[:len(path)] == path
                                      for old in self.paths)
                self.paths.add(path)
            self.receivers, self.blocks = receivers, blocks
            self.votes, self.proposals = votes, proposals
        self.actions.append((action, error))
        self.transitions.append(dict(action_index=len(self.actions), receivers={
            who: dict(before=self.signing_state(v), after=self.signing_state(self.receivers[who]))
            for who, v in before_receivers.items()
            if self.signing_state(v) != self.signing_state(self.receivers[who])}))
        if self.trace:
            print(f'{len(self.actions)} {action!r} => {error or "accepted"}', flush=True)
        return error

    def latest_target(self, who):
        v = self.receivers[who]
        return v.tip if v.latest is None else v.vote(v.latest).target

    @staticmethod
    def signing_state(v):
        return dict(latest_vote=v.latest,
                    latest_target=None if v.latest is None else v.vote(v.latest).target,
                    selected_tip=v.tip, finalized=v.finalized)

    def prior_position_votes(self, who, parent):
        v = self.receivers[who]
        position = (parent, v.block(parent).height + 1)
        return [vote.id for vote in v.self_branch(v.latest)
                if vote.signer == who and
                (v.block(vote.target).parent, v.block(vote.target).height) == position]

    def progress_diagnostics(self):
        """Admitted evidence is reusable support, not permission for a new signature.

        A spent position cannot be repaired by retrying a fresh own proposal.
        Deliver existing evidence separately; replay does not move latest Vote.
        These local restrictions do not establish permanent network deadlock.
        """
        return {who: dict(**self.signing_state(v),
                         proposal_parent=self.owner(who).proposal_parent(),
                         prior_position_votes=self.prior_position_votes(who, self.latest_target(who)),
                         admitted_parent_votes=[vote.id for vote in v.votes
                                                if vote.target == self.latest_target(who)],
                         admitted_tip_votes=[vote.id for vote in v.votes if vote.target == v.tip])
                for who, v in self.receivers.items()}

    def honest_vote(self, who):
        """Return None on acceptance, otherwise a refusal reason."""
        target = best_endorseable(self.receivers[who])
        if target is not None:
            race, signature = self.signing_material(who, target)
            return self.step(('sign_vote', who, target, self.alloc(), race, signature))
        return 'no eligible Vote target'

    def honest_proposal(self, who):
        """Return None on acceptance, otherwise a refusal reason."""
        # proposal_parent includes the Python-only actionable projection and
        # historical-parent route; both still require a Go port.
        target = self.owner(who).proposal_parent()
        if target is not None:
            return self.step(('propose', who, target, self.alloc(), self.alloc(),
                              self.rank(who), self.rank(who)))
        return 'no eligible proposal parent'
