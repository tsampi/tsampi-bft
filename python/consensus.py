"""Symbolic consensus rules for exact-ancestry fork choice and finality.

Symbolic identities/races and evidence-driven authority removal. No crypto,
transactions, Epic changes, persistence, or timing. Race is already
ranked: higher wins; equal ranks prefer the smaller first-divergent Block ID.
Transitions return new Validators; failures leave the input unchanged.
The evidence resolver supplies finite test evidence, not a refinement proof.
"""
from dataclasses import dataclass, replace
from functools import cached_property, cmp_to_key

from primitives import (
    Block,
    Evidence,
    ModelError,
    RecordedExclusion,
    State,
    Vote,
    require,
)
from quorum import (
    QuorumHit,
    frontier,
    has_quorum,
    scan_quorum,
    support_view,
)

CACHE_ENABLED = True
CACHE_LIMIT = 256


def remember(v, key, value):
    if CACHE_ENABLED:
        if len(v._memo) >= CACHE_LIMIT:
            v._memo.pop(next(iter(v._memo)))
        v._memo[key] = value
    return value


@dataclass(frozen=True)
class Validator:
    identity: int | None  # None is an observer; observers cannot sign.
    blocks: tuple[Block, ...]  # Newest first, as in Lean.
    votes: tuple[Vote, ...]
    tip: int
    latest: int | None
    finalized: int  # Monotone stored checkpoint, distinct from historical_q3(tip).
    emitted: tuple[Vote, ...] = ()  # Local signatures only; reception never appends.
    # Python-model-only authenticated closure for rejected conflict objects.
    # Go does not yet expose this resolver. Side objects supply no live support.
    # An admitted descendant may activate the specific ancestor Block bodies it
    # needs; conflicting Votes remain side-only. See Node._receive_evidence_proposal.
    evidence_blocks: tuple[Block, ...] = ()
    evidence_votes: tuple[Vote, ...] = ()
    portable_evidence: tuple[Evidence, ...] = ()

    @cached_property
    def _memo(self):
        # replace() constructs a fresh object: caches never cross snapshots.
        return {}

    @cached_property
    def _block_index(self):
        return {b.id: b for b in reversed(self.blocks)}

    @cached_property
    def _vote_index(self):
        return {vote.id: vote for vote in reversed(self.votes)}

    @classmethod
    def init(cls, genesis, identity):
        require(genesis.parent is None and genesis.height == 0 and
                genesis.proposer_vote is None and not genesis.endorsements and
                not genesis.exclusions and
                genesis.settled is None, 'invalid genesis shape')
        s = genesis.state
        require(0 < s.numerator <= s.denominator, 'invalid threshold')
        require(s.members and all(weight > 0 for _, weight in s.members) and
                len({who for who, _ in s.members}) == len(s.members), 'invalid membership')
        require(s.stake(identity) > 0, 'unknown validator')
        return cls(identity, (genesis,), (), genesis.id, None, genesis.id)

    @classmethod
    def observer(cls, genesis):
        """Construct a credential-free receiver over the same public state."""
        require(bool(genesis.state.members), 'invalid membership')
        seeded = cls.init(genesis, genesis.state.members[0][0])
        return replace(seeded, identity=None)

    def block(self, id):
        if CACHE_ENABLED:
            if id in self._block_index:
                return self._block_index[id]
            raise ModelError(f'missing Block {id}', 'missing_block', id)
        for b in self.blocks:
            if b.id == id:
                return b
        raise ModelError(f'missing Block {id}', 'missing_block', id)

    def vote(self, id):
        if CACHE_ENABLED:
            if id in self._vote_index:
                return self._vote_index[id]
            raise ModelError(f'missing Vote {id}', 'missing_vote', id)
        for vote in self.votes:
            if vote.id == id:
                return vote
        raise ModelError(f'missing Vote {id}', 'missing_vote', id)

    def ancestry(self, id):
        key = 'ancestry', id
        if CACHE_ENABLED and key in self._memo:
            return self._memo[key]
        path = []
        for _ in range(len(self.blocks) + 1):
            b = self.block(id)
            path.append(b)
            if b.parent is None:
                return remember(self, key, tuple(reversed(path)))
            id = b.parent
        raise ModelError('cyclic ancestry')

    def self_branch(self, id):
        if self.evidence_votes:
            # A live Vote may name an authenticated predecessor whose
            # target proposal was rejected and retained evidence-only.  Follow
            # that exact signed history through the resolver without adding any
            # side Vote to the live iterable inventory.
            return evidence_source(self).self_branch(id)
        branch = []
        for _ in range(len(self.votes) + 1):
            if id is None:
                return branch
            vote = self.vote(id)
            branch.append(vote)
            id = vote.prev_self
        raise ModelError('cyclic self-vote history')


def evidence_source(v):
    """Resolve authenticated proof dependencies without making them live.

    The returned value is an ephemeral historical resolver.  Consensus code
    must never publish or install it: its merged stores are only for evidence
    verification and the historical queries that verification requires.
    """
    if not v.evidence_blocks and not v.evidence_votes:
        return v

    def merged(live, side, kind):
        result = {item.id: item for item in live}
        for item in side:
            require(item.id not in result or result[item.id] == item,
                    f'{kind} identity collision')
            result.setdefault(item.id, item)
        return tuple(result.values())

    return replace(
        v,
        blocks=merged(v.blocks, v.evidence_blocks, 'Block'),
        votes=merged(v.votes, v.evidence_votes, 'Vote'),
        evidence_blocks=(),
        evidence_votes=(),
    )


# Historical quorum and finality queries. Pure ancestry scans live in quorum.py;
# these wrappers bind them to one immutable Validator snapshot and its cache.
def block_frontier(v, id):
    """Q1 of this exact historical Block, including only its own anchor."""
    key = 'frontier', id
    if CACHE_ENABLED and key in v._memo:
        return v._memo[key]
    b = v.block(id)
    anchor = v.block(b.settled) if b.settled is not None else None
    return remember(v, key, frontier(v.ancestry(id)[::-1], anchor))


def quorums(v, id):
    """Historical Q1 and Q2 of one immutable Block, independent of node finality."""
    q1 = block_frontier(v, id)
    return q1, block_frontier(v, q1.block.id)


def historical_q3(v, id):
    """Q1(Q1(Q1(id))), not the receiver's stored finalized checkpoint."""
    return block_frontier(v, quorums(v, id)[1].block.id)


# Authenticated knowledge closure. These walks determine what a signed action
# can prove it knew; they do not turn evidence-only objects into live inventory.
@dataclass(frozen=True)
class KnownObjects:
    votes: tuple[Vote, ...]
    blocks: tuple[Block, ...]


def known_objects_cutoff(v, vote, n):
    """Height of Q1^n(vote.target), using the unchanged frontier/scan_quorum.

    Q1^0 is the target itself, not its first quorum. Genesis is absorbing,
    including a short history with no completed quorum. Each step restarts the
    existing scan at the previous Q1 (as quorums does for Q2), NOT at h - 1.
    Computing this anchor requires the target's complete admitted ancestry.
    No discounting or receiver-local gossip participates in this calculation.
    """
    require(isinstance(n, int) and n >= 0, 'invalid quorum window')
    target = v.block(vote.target)
    if n == 0:
        return target.height
    path = v.ancestry(target.id)[::-1]
    # Duty windows use raw authenticated support, not consensus credit.
    # Preserve each signature's original N=2 obligation.
    support = {}
    for b in path:
        for endorsement in b.endorsements:
            support.setdefault(endorsement.target, set()).add(endorsement.signer)
    for _ in range(n):
        hit = frontier(path, support=support)
        if hit.block.parent is None:
            return hit.block.height
        path = (hit.block,) + hit.older
    return path[0].height


def known_objects(v, vote, n, *, paths=None):
    """Read-only required closure with one fixed Q1^n target-height cutoff."""
    key = 'known', vote, n
    if paths is None and CACHE_ENABLED and key in v._memo:
        return v._memo[key]
    result = known_objects_since(v, vote, known_objects_cutoff(v, vote, n), paths=paths)
    return remember(v, key, result)


def known_objects_since(v, vote, cutoff_height, *, paths=None, include_evidence=False):
    """Collect authenticated dependencies at/above an inclusive fixed height.

    Blocks use block.height; Votes use their endorsed target height (height-1),
    NOT their next-proposal height. Thus a boundary Block is included, but its
    carried parent Votes normally are not. Cross-boundary objects must be
    available to read their authenticated headers; their outgoing edges are not
    expanded. Off-fork objects use the SAME cutoff. N=0 in known_objects keeps
    the root target's height band; Genesis/large N reaches height zero.

    Input objects must already be authenticated/admitted (or a prospective root
    built from authenticated references). This is not an admission/crypto check:
    older headers are trusted, and ranking, Stake and signature rules are not
    replayed. Structural errors encountered in the expanded graph raise invalid
    ModelError; unavailable references retain missing_vote/missing_block kinds.
    No partial result is returned. A height window is not an object-count bound.

    prev_vote is an INNER identity: resolve it through the target's exact embedded
    proposer_vote, never by outer ID or by enumerating matching receiver Votes.
    Embedded block Votes need not separately occur in v.votes. prev_self does
    require the exact outer Vote in v.votes. The detached self-Vote of a proposal
    is not a Block dependency; block.proposer_vote is the parent endorsement.

    Results are ID-sorted, deduplicated separately by type. Optional paths is an
    output dict keyed by ('vote'/'block', id), populated only on success, separate
    from the public object result. Paths use fixed edge order, then Vote ID order.
    Iterative DFS distinguishes shared references from active cycles.
    The live-permission query can also follow verified proof references and
    their causes; ordinary accountability windows keep their original edges.
    """
    if include_evidence:
        v = evidence_source(v)
    root_target = v.block(vote.target)
    require(vote.height == root_target.height + 1, 'wrong Vote position')
    require(isinstance(cutoff_height, int) and
            0 <= cutoff_height <= root_target.height, 'invalid cutoff height')
    stores = {'vote': {}, 'block': {}}
    for kind, objects in (('vote', v.votes), ('block', v.blocks)):
        for obj in objects:
            stores[kind].setdefault(obj.id, []).append(obj)
    observed, active, done, included, routes = {}, set(), set(), {}, {}

    def resolve(kind, id):
        objects = stores[kind].get(id, ())
        if not objects:
            raise ModelError(f'missing {kind.title()} {id}', 'missing_' + kind, id)
        require(all(obj == objects[0] for obj in objects), f'{kind.title()} identity collision')
        return objects[0]

    def evidence_edges(proofs):
        pending, seen, identities = list(proofs), set(), set()
        while pending:
            proof = pending.pop()
            if id(proof) in seen:
                continue
            seen.add(id(proof))
            identities.update(proof.votes)
            pending.extend(proof.causes)
        return [('evidence', 'vote', resolve('vote', identity))
                for identity in sorted(identities)]

    # A leave marker avoids Python recursion limits on long valid histories.
    stack: list = [('vote', vote, (f'vote:{vote.id}',) if paths is not None else (), False)]
    while stack:
        kind, obj, route, leave = stack.pop()
        key = kind, obj.id
        if leave:
            active.remove(key)
            done.add(key)
            continue
        require(key not in observed or observed[key] == obj, f'{kind.title()} identity collision')
        require(all(old == obj for old in stores[kind].get(obj.id, ())),
                f'{kind.title()} identity collision')
        observed[key] = obj
        require(key not in active, 'cyclic known objects')
        if key in done:
            continue
        height = obj.height - 1 if kind == 'vote' else obj.height
        require(height >= 0, 'invalid object height')
        if height < cutoff_height:
            done.add(key)
            continue
        included[key] = obj
        if paths is not None:
            routes[key] = route
        edges = []
        if kind == 'vote':
            target = resolve('block', obj.target)
            predecessor = target.proposer_vote
            check_vote_target(target, obj)
            if obj.prev_self is not None:
                previous = resolve('vote', obj.prev_self)
                require((previous.signer, previous.chain) == (obj.signer, obj.chain),
                        'wrong predecessor signer or chain')
                edges.append(('prev_self', 'vote', previous))
            if predecessor is not None:
                edges.append(('prev_vote', 'vote', predecessor))
            edges.append(('target', 'block', target))
            if include_evidence:
                edges.extend(evidence_edges(obj.exclusions))
        elif obj.parent is None:
            require(obj.height == 0 and obj.proposer_vote is None and not obj.endorsements,
                    'invalid genesis shape')
        else:
            parent = resolve('block', obj.parent)
            require(obj.height == parent.height + 1, 'wrong Block height')
            require(obj.proposer_vote is not None, 'missing proposer Vote')
            require(obj.proposer_vote.signer == obj.proposer and
                    obj.proposer_vote.target == obj.parent and
                    obj.proposer_vote in obj.endorsements,
                    'proposer Vote not in admission batch')
            edges = [('parent', 'block', parent), ('proposer_vote', 'vote', obj.proposer_vote)]
            edges.extend(('endorsements', 'vote', x)
                         for x in sorted(obj.endorsements, key=lambda x: x.id))
            if include_evidence:
                edges.extend(evidence_edges(record.proof for record in obj.exclusions))
        active.add(key)
        stack.append((kind, obj, route, True))
        for edge, child_kind, child in reversed(edges):
            stack.append((child_kind, child,
                          route + (f'{edge}->{child_kind}:{child.id}',) if paths is not None else (), False))
    result = KnownObjects(tuple(included[k] for k in sorted(included) if k[0] == 'vote'),
                          tuple(included[k] for k in sorted(included) if k[0] == 'block'))
    if paths is not None:
        paths.update(routes)
    return result


def target_at_or_above(v, target_id, boundary_id):
    """Inclusive exact ancestry; equal-height forks are incomparable."""
    return any(b.id == boundary_id for b in v.ancestry(target_id))


# Evidence verification and retention. Fault history stays separate from the
# authority calculation for a new action below.
def _root_boundary(v, vote):
    """An available blank root's signed Q3 bounds its later valid self path."""
    if vote.prev_self is None:
        try:
            return historical_q3(v, vote.target).block.id
        except ModelError:
            # Positive ordering of known headers needs no retired target body.
            # Without that ordering the normal activity query remains fallible.
            pass
    return None


def _self_path_contains(v, predecessor, wanted, boundary=None):
    for _ in range(len(v.votes) + 1):
        if predecessor is None:
            return False
        if predecessor == wanted:
            return True
        previous = v.vote(predecessor)
        if boundary is not None and not target_at_or_above(v, previous.target, boundary):
            return False
        predecessor = previous.prev_self
    raise ModelError('cyclic self-vote history')


def direct_conflict(v, a, b):
    """Mutually active signatures must belong to one valid recent signed path.

    A missing predecessor is unavailable evidence, never a disconnected path.
    A blank root's signed Q3 bounds its later path: a known target outside that
    subtree proves the path cannot validly link that root, without fetching its
    retired prefix. Physical links beyond this cut cannot excuse a Q3 retreat.
    Only referenced immutable objects affect the verdict, so an unrelated later
    signature cannot retroactively join two roots.
    """
    v = evidence_source(v)
    if not (a.id != b.id and a.signer == b.signer and a.chain == b.chain):
        return False
    # A signer gets one action per exact Block, not one action for the whole
    # PrevVoteHash position. Different Blocks may legitimately share that
    # position; their ordinary self-history is checked below.
    if a.prev_vote == b.prev_vote and a.target == b.target:
        return True
    if a.prev_self is not None and a.prev_self == b.prev_self:
        return True
    # Go proves a known linked prefix before resolving target/Q3 dependencies.
    # A retired root may be absent without invalidating this positive ordering.
    unavailable = None
    for first, second in ((a, b), (b, a)):
        try:
            if _self_path_contains(v, first.prev_self, second.id, _root_boundary(v, second)):
                return False
        except ModelError as error:
            unavailable = unavailable or error
    if not (target_at_or_above(v, a.target, historical_q3(v, b.target).block.id)
            and target_at_or_above(v, b.target, historical_q3(v, a.target).block.id)):
        return False
    if unavailable is not None:
        raise unavailable
    return True


def verify_evidence(v, proof):
    """Verify a portable proof against admitted authenticated objects.

    Derived edges must be exact required proofs omitted by the named signature.
    Recursive verification bottoms in two distinct signed successors.
    """
    v = evidence_source(v)
    pending, seen = [proof], set()
    while pending:
        item = pending.pop()
        if id(item) in seen:
            continue
        seen.add(id(item))
        if not item.causes:
            require(item.duty_floor == 0, 'direct evidence duty floor must be zero')
            require(len(item.votes) == 2, 'invalid direct evidence')
            a, b = (v.vote(vote_id) for vote_id in item.votes)
            require(a.signer == item.offender and direct_conflict(v, a, b),
                    'invalid direct evidence')
        else:
            require(len(item.votes) == 1, 'invalid derived evidence')
            vote = v.vote(item.votes[0])
            minimum = historical_q3(v, vote.target).block.height
            require(isinstance(item.duty_floor, int) and
                    minimum <= item.duty_floor <= v.block(vote.target).height,
                    'invalid evidence duty floor')
            causes = accounting_causes(v, vote,
                required_exclusions_at(v, vote, item.duty_floor))
            require(vote.signer == item.offender and all(
                cause in causes for cause in item.causes), 'invalid derived evidence')
            pending.extend(item.causes)
    return True


def _evidence_vote(v, identity):
    try:
        return v.vote(identity)
    except ModelError as error:
        if error.kind != 'missing_vote':
            raise
        # A required closure can name an embedded action before stage_block
        # submits the batch. Read its header without adding live support.
        carried = [vote for block in v.blocks for vote in block.endorsements
                   if vote.id == identity]
        if not carried:
            raise
        require(all(vote == carried[0] for vote in carried), 'Vote identity collision')
        return carried[0]


def equivocation_parent(v, proof):
    """Exact parent of distinct conflicting sibling actions, if established.

    Callers verify the proof first. A general self-history fault or a derived
    accounting fault still proves misconduct, but does not name a sibling slot.
    """
    if proof.causes or len(proof.votes) != 2:
        return None
    v = evidence_source(v)
    first, second = (_evidence_vote(v, identity) for identity in proof.votes)
    if (first.signer != proof.offender or second.signer != proof.offender or
            first.chain != second.chain):
        return None
    if first.target == second.target:
        return first.target
    left, right = v.block(first.target), v.block(second.target)
    return left.parent if left.parent is not None and left.parent == right.parent else None


def _evidence_key(v, proof):
    return proof.offender, _evidence_vote(v, proof.votes[0]).chain, equivocation_parent(v, proof)


def evidence_fork_positions(v, proof):
    """Proposal positions targeted by the first diverging signed actions.

    Only an offender proposal at the actual signing fork is cut. Later
    proposals on either signing history remain distinct from that fault.
    Callers authenticate and verify the proof before activating these cuts.
    """
    if proof.causes:
        return ()
    v = evidence_source(v)
    first, second = (_evidence_vote(v, identity) for identity in proof.votes)
    parent = equivocation_parent(v, proof)
    if parent is not None:
        return ((proof.offender, first.chain, parent),)
    boundary = _root_boundary(v, first) if first.prev_self is None else _root_boundary(v, second)
    children, unavailable = {}, None
    current = first
    for _ in range(len(v.votes) + 1):
        if boundary is not None and not target_at_or_above(v, current.target, boundary):
            return ()
        predecessor = current.prev_self
        require(predecessor not in children, 'cyclic self-vote history')
        children[predecessor] = current
        if predecessor is None:
            break
        try:
            current = v.vote(predecessor)
        except ModelError as error:
            if error.kind != 'missing_vote':
                raise
            unavailable = error
            break
    else:
        raise ModelError('cyclic self-vote history')
    current, seen = second, set()
    for _ in range(len(v.votes) + 1):
        if boundary is not None and not target_at_or_above(v, current.target, boundary):
            return ()
        require(current.id not in seen, 'cyclic self-vote history')
        seen.add(current.id)
        predecessor = current.prev_self
        if predecessor in children:
            other = children[predecessor]
            if other.id == current.id:
                return ()
            successors = other, current
            break
        if predecessor is None:
            if unavailable is not None:
                raise unavailable
            return ()
        current = v.vote(predecessor)
    else:
        raise ModelError('cyclic self-vote history')
    if (target_at_or_above(v, successors[0].target, successors[1].target) or
            target_at_or_above(v, successors[1].target, successors[0].target)):
        return ()
    positions = set()
    for successor in successors:
        proposal = v.block(successor.target)
        if proposal.proposer == proof.offender and proposal.parent is not None:
            positions.add((proof.offender, first.chain, proposal.parent))
    return tuple(sorted(positions))


def canonical_evidence(v, proofs):
    # Preserve explicit parent witnesses and general witnesses for every cut.
    # General faults without a proposal cut still remove stake once per signer.
    v = evidence_source(v)
    selected = {}
    for proof in sorted(proofs, key=repr):
        key = _evidence_key(v, proof)
        positions = evidence_fork_positions(v, proof) if key[2] is None else ()
        parents = tuple(position[2] for position in positions) or (None,)
        for parent in parents:
            selected.setdefault((*key, parent), proof)
    keys = sorted(selected, key=lambda key: (
        key[0], key[1], key[2] is not None, key[2] if key[2] is not None else 0,
        key[3] is not None, key[3] if key[3] is not None else 0))
    return tuple(dict.fromkeys(selected[key] for key in keys))


def retain_evidence_only(v, blocks=(), votes=(), proofs=()):
    """Retain a verified rejected closure without admitting consensus objects.

    This is an executable Python abstraction of the resolver required by the
    handoff.  Current Go drops this closure on the corresponding rejection
    path, so GREEN results here must be ported and retested in Go.
    """
    live_blocks = {block.id: block for block in v.blocks}
    live_votes = {vote.id: vote for vote in v.votes}

    def retained(existing, additions, live, kind):
        result = {item.id: item for item in existing}
        for item in additions:
            require(item.id not in live or live[item.id] == item,
                    f'{kind} identity collision')
            require(item.id not in result or result[item.id] == item,
                    f'{kind} identity collision')
            if item.id not in live:
                result.setdefault(item.id, item)
        return tuple(result.values())

    staged = replace(
        v,
        evidence_blocks=retained(v.evidence_blocks, blocks, live_blocks, 'Block'),
        evidence_votes=retained(v.evidence_votes, votes, live_votes, 'Vote'),
    )
    for proof in proofs:
        verify_evidence(staged, proof)
    return replace(staged, portable_evidence=canonical_evidence(staged,
        (*v.portable_evidence, *proofs)))


# Evidence-derived authority. required_exclusions_at answers a duty query;
# classify_known_blocks later answers a transition-knowledge query.
def accounting_causes(v, vote, needed):
    missing = tuple(e for e in needed if e.offender not in
                    {p.offender for p in vote.exclusions})
    if needed or vote.exclusions:
        try:
            # Admitted Votes have already had these proofs verified.  Reuse the
            # recursion-free direction classifier so an authorized move is not
            # turned into evidence against its honest signer.
            classify_target_transition(evidence_source(v), vote,
                                       vote.exclusions)
            classify_known_blocks(evidence_source(v), vote, vote.exclusions)
        except ModelError as error:
            if error.kind != 'invalid':
                raise
            # A carried portable proof also proves the signer's knowledge,
            # even when that proof lies outside the ordinary N=2 duty walk.
            return canonical_evidence(v, (*needed, *vote.exclusions))
    return missing


def required_exclusions(v, root):
    """Accountability starts at the exact target's immutable Q3 boundary."""
    source = evidence_source(v)
    return required_exclusions_at(
        source, root, historical_q3(source, root.target).block.height)


def required_exclusions_at(v, root, duty_floor):
    """Raw N=2 duties bounded by one inherited finalized floor.

    A dependency can raise the inherited floor to its own Q3, but never lower it.
    Every derived accusation records the exact floor used for its named Vote.
    Missing active edges remain errors; unavailable bytes never select a window.
    """
    def normalized(vote, floor):
        require(isinstance(floor, int) and 0 <= floor <= v.block(vote.target).height,
                'invalid duty floor')
        return max(floor, historical_q3(v, vote.target).block.height)

    initial = normalized(root, duty_floor)
    memo, active = {}, set()
    stack: list[tuple[Vote, int, KnownObjects | None]] = [(root, initial, None)]
    while stack:
        current, floor, closure = stack.pop()
        identity = current.id, floor
        key = 'required', current, floor
        if identity in memo:
            continue
        if CACHE_ENABLED and key in v._memo:
            memo[identity] = v._memo[key]
            continue
        if closure is None:
            require(current.id not in active, 'cyclic accountability')
            active.add(current.id)
            cutoff = max(floor, known_objects_cutoff(v, current, 2))
            closure = known_objects_since(v, current, cutoff)
            stack.append((current, floor, closure))
            stack.extend((vote, normalized(vote, floor), None)
                         for vote in reversed(closure.votes)
                         if vote.id != current.id and
                         (vote.id, normalized(vote, floor)) not in memo)
            continue
        proofs = [e.proof for b in closure.blocks for e in b.exclusions]
        groups = {}
        for vote in closure.votes:
            if vote.id == current.id:
                continue
            group_key = vote.signer, vote.chain
            for other in groups.setdefault(group_key, []):
                if direct_conflict(v, other, vote):
                    proofs.append(Evidence(vote.signer, tuple(sorted((other.id, vote.id)))))
            groups[group_key].append(vote)
            dependency_floor = normalized(vote, floor)
            causes = accounting_causes(v, vote, memo[vote.id, dependency_floor])
            proofs.extend(vote.exclusions)
            if causes:
                proofs.append(Evidence(vote.signer, (vote.id,), causes, dependency_floor))
        active.remove(current.id)
        memo[identity] = remember(v, key, canonical_evidence(v, proofs))
    return memo[root.id, initial]


def block_exclusions(v, b):
    # The prospective Block is unsigned here. Its closure has no detached Vote.
    inherited = {e.offender: e for e in v.block(b.parent).exclusions}
    supplied = tuple(e.proof for e in b.exclusions)
    for proof in supplied:
        verify_evidence(v, proof)
    b = replace(b, exclusions=())
    staged = replace(v, blocks=(b,) + v.blocks)
    probe = Vote(-1, -1, b.proposer, b.state.chain, b.height + 1,
                 b.proposer, b.proposer_vote.inner_id, b.id,
                 b.state.stake(b.proposer), None, 0, 0)
    proofs = canonical_evidence(staged, (*[e.proof for e in v.block(b.parent).exclusions],
                                 *required_exclusions(staged, probe), *supplied))
    return tuple(RecordedExclusion(proof, inherited[proof.offender].recorded_height
                                   if proof.offender in inherited else b.height)
                 for proof in proofs)


def observed_evidence(v):
    """Strict admitted-history audit; missing dependencies remain errors.

    Local actions use view_evidence instead, which activates only available
    verified proofs and includes explicit evidence-side proofs.
    """
    proofs, groups = [], {}
    for vote in sorted(v.votes, key=lambda vote: vote.id):
        key = vote.signer, vote.chain
        for previous in groups.setdefault(key, []):
            if direct_conflict(v, previous, vote):
                proofs.append(Evidence(vote.signer, (previous.id, vote.id)))
        groups[key].append(vote)
        proofs.extend(vote.exclusions)
        causes = accounting_causes(v, vote, required_exclusions(v, vote))
        if causes:
            proofs.append(Evidence(vote.signer, (vote.id,), causes,
                                   historical_q3(v, vote.target).block.height))
    return canonical_evidence(v, proofs)


def available_observed_evidence(v):
    """Derive only proofs whose complete dependencies are locally available.

    Retired standalone history can be absent while ordinary consensus remains
    live.  Such an unavailable proof is not activated in the local action view;
    independently verifiable live proofs and explicit evidence-only proofs are.
    """
    proofs, groups = [], {}

    def include(proof):
        try:
            verify_evidence(v, proof)
        except ModelError as error:
            if error.kind not in ('missing_vote', 'missing_block'):
                raise
            return
        proofs.append(proof)

    # A Block record is itself a top-level proof.  Do not lose its offender
    # merely because a later omitting Vote turns that proof into a nested cause.
    for block in v.blocks:
        for record in block.exclusions:
            include(record.proof)
    for vote in sorted(v.votes, key=lambda vote: vote.id):
        key = vote.signer, vote.chain
        for previous in groups.setdefault(key, []):
            try:
                if direct_conflict(v, previous, vote):
                    include(Evidence(vote.signer,
                                     tuple(sorted((previous.id, vote.id)))))
            except ModelError as error:
                if error.kind not in ('missing_vote', 'missing_block'):
                    raise
        groups[key].append(vote)
        for proof in vote.exclusions:
            include(proof)
        try:
            causes = accounting_causes(v, vote, required_exclusions(v, vote))
        except ModelError as error:
            if error.kind not in ('missing_vote', 'missing_block'):
                raise
            continue
        if causes:
            proof = Evidence(vote.signer, (vote.id,), causes,
                             historical_q3(v, vote.target).block.height)
            verify_evidence(v, proof)
            proofs.append(proof)
    return canonical_evidence(v, proofs)


def view_evidence(v):
    """Verified local evidence used only for action selection and generation.

    Rejected evidence-only Votes are not scanned as ordinary accountability
    history.  Only the direct proofs verified when they were retained are
    added to the ordinary admitted-history evidence view.
    """
    for proof in v.portable_evidence:
        verify_evidence(v, proof)
    return canonical_evidence(v, (*available_observed_evidence(v),
                               *v.portable_evidence))


def authority_after_evidence(v, parent_id, proofs=()):
    """Immediate authority for a new proof-bound action on any parent fork.

    Historical Blocks keep their recorded state. A new child applies verified
    carried evidence immediately, including when its carrier is not finalized.
    """
    parent = v.block(parent_id)
    proofs = tuple(proofs)
    for proof in proofs:
        verify_evidence(v, proof)
    return parent.state.without(
        {record.offender for record in parent.exclusions} |
        {proof.offender for proof in proofs})


# Ranking, transition classification, and finite candidate inventory.
def quorum_stake(path, anchor=None):
    support = support_view(path)
    hit = scan_quorum(path, anchor, support)
    window = path[::-1]
    if hit is not None:
        index = next(i for i, b in enumerate(window) if b.id == hit.block.id)
        window = window[index + 1:]
    if not window:
        return 0
    signers = {signer for b in window[:-1] for signer in support.get(b.id, ())}
    return sum(window[0].state.stake(who) for who in signers)


def check_block_improvement(v, b):
    require(b.parent is not None, 'live Block has no parent')
    old_path = v.ancestry(b.parent)[::-1]
    path = (b,) + old_path
    anchor = v.block(b.settled) if b.settled is not None else None
    parent = old_path[0]
    old_anchor = v.block(parent.settled) if parent.settled is not None else None
    current = scan_quorum(path, anchor)
    previous = scan_quorum(old_path, old_anchor)
    if (current.block.id if current else None) == (previous.block.id if previous else None):
        progress = quorum_stake(path, anchor) > quorum_stake(old_path, old_anchor)
    else:
        progress = current is not None and (previous is None or
                    any(b.id == previous.block.id for b in current.older))
    # Mandatory parent progress is separate from Vote-target ranking.
    require(progress, 'Block does not advance parent Q1 or unique Stake')


def _ranked_proposal_improves(v, current, previous):
    """The Q2-preserving part of target-switch permission."""
    a, b = v.ancestry(current), v.ancestry(previous)
    require(a[0].id == b[0].id, 'different genesis')
    if current == previous:
        return False
    if any(x.id == previous for x in a):
        return True
    if any(x.id == current for x in b):
        return False

    better_score = fork_order(v, v.block(current), v.block(previous)) < 0
    aq1, aq2 = quorums(v, current)
    bq1, bq2 = quorums(v, previous)
    a_descends = (aq1.block.id != bq2.block.id and
                  target_at_or_above(v, aq1.block.id, bq2.block.id))
    b_descends = (bq1.block.id != aq2.block.id and
                  target_at_or_above(v, bq1.block.id, aq2.block.id))
    q1_nonretreating = target_at_or_above(v, aq1.block.id, bq1.block.id)
    q2_nonretreating = target_at_or_above(v, aq2.block.id, bq2.block.id)
    q2_advances = aq2.block.id != bq2.block.id and q2_nonretreating
    return (q2_advances
            or (better_score and (q1_nonretreating or q2_nonretreating))
            or (a_descends and not b_descends))


def proposal_improves(v, current, previous, *, ordinary_view=None):
    """Shared selected-tip and signed-target switching permission.

    Ranking uses admitted live history. A separate resolver may establish
    certified Q3 catch-up, but cannot promote evidence-only history into ranking.
    """
    live = v if ordinary_view is None else ordinary_view
    direction_error = None
    try:
        if _ranked_proposal_improves(live, current, previous):
            return True
    except ModelError as error:
        if error.kind != 'missing_block':
            raise
        if ordinary_view is None:
            direction_error = error
    try:
        current_q3 = historical_q3(v, current)
        previous_q3 = historical_q3(v, previous)
        _, previous_q2 = quorums(v, previous)
    except ModelError:
        if direction_error is not None:
            raise direction_error
        return False
    permitted = (current_q3.block.id != previous_q3.block.id and
                 any(block.id == previous_q3.block.id for block in current_q3.older) and
                 current_q3.block.height >= previous_q2.block.height)
    if not permitted and direction_error is not None:
        raise direction_error
    return permitted


def classify_known_blocks(v, vote, proofs, *, ordinary_view=None):
    """Require ordinary permission from every known dependency through Q3.

    This is a read-only query over authenticated objects and preverified proofs;
    it never derives exclusions or consults private receiver gossip.
    """
    v = evidence_source(v)
    floor = historical_q3(v, vote.target).block.height
    known = known_objects_since(v, vote, floor, include_evidence=True)
    for block in known.blocks:
        if block.id == vote.target:
            continue
        require(proposal_improves(v, vote.target, block.id,
                                  ordinary_view=ordinary_view),
                f'target lacks switch permission from known Block {block.id}')
    return frozenset()


def classify_target_transition(v, vote, proofs, *, ordinary_view=None):
    """Require shared switch permission from the signed predecessor."""
    if vote.prev_self is None:
        return 'ordinary', frozenset()
    previous = v.vote(vote.prev_self)
    require(proposal_improves(v, vote.target, previous.target,
                              ordinary_view=ordinary_view),
            'target does not improve')
    return 'ordinary', frozenset()


def classify_vote_action(v, vote, proofs, *, ordinary_view=None):
    """Shared predecessor and provable-knowledge action classifier."""
    kind, transition = classify_target_transition(
        v, vote, proofs, ordinary_view=ordinary_view)
    source = evidence_source(v)
    target = source.block(vote.target)
    if target.parent is not None and target.proposer == vote.signer:
        for previous in source.self_branch(vote.prev_self):
            block = source.block(previous.target)
            require((block.parent, block.height) != (target.parent, target.height),
                    'own proposal was not first at position')
    knowledge = classify_known_blocks(v, vote, proofs, ordinary_view=ordinary_view)
    return kind, transition | knowledge


def fork_order(v, left, right, unsigned=None):
    """Order candidates as exact_ancestry_choice.go does."""
    if left.id == right.id:
        return 0

    def path(block):
        return (*v.ancestry(block.parent), block) if block.id == unsigned else v.ancestry(block.id)

    a, b = path(left), path(right)
    for x, y in zip(a, b):
        if x.id != y.id:
            if x.proposer_vote is None or y.proposer_vote is None:
                raise ModelError('missing proposer Vote')
            xr, yr = x.proposer_vote.race, y.proposer_vote.race
            if xr != yr:
                return -1 if xr > yr else 1
            if unsigned in (x.id, y.id):
                return 0
            return -1 if x.id < y.id else 1
    return -1 if len(a) > len(b) else 1


def actionable(v, target):
    return target_at_or_above(v, target, v.finalized)


def selection_vote(v, candidate):
    """Return the exact retained head or the next unsigned local Vote probe."""
    if v.latest is not None and v.vote(v.latest).target == candidate:
        return v.vote(v.latest)
    vote = prospective_vote(v, candidate)
    if v.latest is not None:
        latest = v.vote(v.latest)
        target = v.block(candidate)
        require((latest.signer, latest.chain) == (v.identity, target.state.chain),
                'model selection: local latest unavailable or mismatched')
    return vote


def candidate_selectable(v, candidate):
    """Observers need public improvement; validators also need a valid next Vote."""
    if v.identity is None:
        return True
    try:
        vote = selection_vote(v, candidate)
        if (vote.stake <= 0 or v.identity in {e.offender for e in vote.exclusions}
                or vote_transition_error(v, vote) is not None):
            return False
        check_vote_slot(v, vote)
    except ModelError:
        return False
    return True


def candidate_extends_finalized(v, candidate):
    """Reject a moving candidate whose Q3 would retreat installed finality."""
    try:
        q3 = historical_q3(v, candidate)
    except ModelError:
        return False
    return (q3.block.id == v.finalized or
            any(block.id == v.finalized for block in q3.older))


def _moves_before_replay(v, blocks):
    return [b for b in blocks if b.id != v.tip] + [b for b in blocks if b.id == v.tip]


def model_candidates(v, blocks):
    ordered = _moves_before_replay(v, blocks)
    return tuple(b.id for b in ordered if actionable(v, b.id)
                 and (b.id == v.tip or
                      (proposal_improves(v, b.id, v.tip)
                       and candidate_selectable(v, b.id)
                       and candidate_extends_finalized(v, b.id))))


def best_model_candidate(v, blocks):
    return next(iter(model_candidates(v, blocks)), None)


def observed_frontier(v):
    blocks = [b for b in v.blocks if actionable(v, b.id)]
    parents = {b.parent for b in blocks}
    return sorted((b for b in blocks if b.id not in parents),
                  key=cmp_to_key(lambda a, b: fork_order(v, a, b)))


def actionable_frontier(v):
    return tuple(observed_frontier(v))


def live_selection_candidates(v):
    tips = actionable_frontier(v)
    inventory = []
    if tips:
        blocks = sorted((b for b in v.blocks
                         if b.height == tips[0].height and actionable(v, b.id)
                         and not any(tip.id != b.id and
                                     target_at_or_above(v, tip.id, b.id) for tip in tips)),
                        key=cmp_to_key(lambda a, b: fork_order(v, a, b)))
        inventory.extend(blocks)
    inventory.extend(tips)
    inventory.append(v.block(v.tip))
    return tuple(dict.fromkeys(model_candidates(v, inventory)))


def best_endorseable(v):
    return next(iter(live_selection_candidates(v)), None)


def observed_q3(v):
    """Deepest compatible Q3 derived only from the admitted public frontier.

    Honest execution makes these frontiers ancestry-comparable. Refuse an
    inventory that violates that safety boundary instead of resolving it with
    a receipt-order or hash tie break.
    """
    deepest = v.block(v.finalized)
    for tip in observed_frontier(v):
        candidate = historical_q3(v, tip.id).block
        if target_at_or_above(v, candidate.id, deepest.id):
            deepest = candidate
        elif not target_at_or_above(v, deepest.id, candidate.id):
            raise ModelError('conflicting observed Q3 frontiers')
    return deepest


# Vote admission and local generation. Authentication, slot, history, and
# transition checks stay explicit and ordered; owner.py owns durable signing.
def require_finalized_lineage(v, target):
    require(actionable(v, target),
            'Block is outside current finalized lineage')


def self_segment_active(v, head, target_id):
    """Keep a signed segment while any of its targets reaches the new Q3.

    One active target suffices; proving retirement requires the whole segment.
    An off-fork head can still carry an earlier active obligation. Missing
    dependencies needed to decide activity remain unavailable.
    """
    source = evidence_source(v)
    boundary = historical_q3(source, target_id).block.id
    current = head
    for _ in range(len(source.votes) + 1):
        require((current.signer, current.chain) == (head.signer, head.chain),
                'wrong predecessor signer or chain')
        if target_at_or_above(source, current.target, boundary):
            return True
        if current.prev_self is None:
            return False
        current = source.vote(current.prev_self)
    raise ModelError('cyclic self-vote history')


def check_vote_reset(v, vote):
    """Reject an active blank-root conflict in either arrival order.

    This is fresh-action policy. Certificate replay continues to authenticate
    historical signatures and derive their faults without a private-gossip veto.
    """
    source = evidence_source(v)
    for old in source.votes:
        if vote.prev_self is None or old.prev_self is None:
            require(not direct_conflict(source, old, vote),
                    'conflicting active self-vote history')


def prospective_vote(v, target_id, id=-1, race=0, sig_hash=0):
    """Unsigned local Vote context; selection never inserts the probe ID."""
    target = v.block(target_id)
    if v.latest is None:
        predecessor = None
    else:
        head = v.vote(v.latest)
        require((head.signer, head.chain) == (v.identity, target.state.chain),
                'local signing: authenticated local latest unavailable or mismatched')
        predecessor = v.latest if self_segment_active(v, head, target_id) else None
    vote = Vote(id, id, v.identity, target.state.chain, target.height + 1,
                target.proposer, target.proposer_vote.inner_id if target.proposer_vote else None,
                target_id, target.state.stake(v.identity), predecessor, race, sig_hash)
    # A signer gets one durable action for each exact Block. PrevVoteHash is
    # fixed by that Block's header, so it is not a slot shared by its siblings.
    occupied = next((old for old in evidence_source(v).votes
                     if (old.signer, old.chain, old.target) ==
                     (vote.signer, vote.chain, vote.target)), None)
    if occupied is not None:
        possible_replay = (occupied.prev_self == vote.prev_self and
                           occupied.race == vote.race and
                           occupied.sig_hash == vote.sig_hash)
        require(possible_replay, 'double vote for exact Block')
    # An unsigned possible replay must be compared under its stored identity.
    # The owner still checks the complete evidence-bound body before reuse.
    check_vote_reset(v, replace(vote, id=occupied.id) if occupied is not None else vote)
    return replace(vote, exclusions=exception_aware_exclusions(v, vote))


def exception_aware_exclusions(v, vote):
    """Bind every available verified proof into the next fresh signature."""
    proofs = canonical_evidence(v, (*required_exclusions(v, vote), *view_evidence(v)))
    classify_vote_action(v, replace(vote, exclusions=proofs), proofs)
    return proofs


def vote_transition_error(v, vote):
    try:
        classify_vote_action(v, vote, vote.exclusions)
    except ModelError as error:
        if error.kind != 'invalid':
            raise
        return str(error)
    return None


def advance_coverage(v, candidate):
    require_finalized_lineage(v, candidate)
    require_finalized_lineage(v, v.tip)
    tip = candidate
    if (v.identity is not None and candidate != v.tip
            and not candidate_selectable(v, candidate)):
        tip = v.tip
    q3 = observed_q3(v)
    # Public Q3 may advance even when this validator cannot make the optional
    # tip move. Keep the installed tip on the finalized lineage without
    # pretending that the private next-Vote gate succeeded.
    if not target_at_or_above(v, tip, q3.id):
        tip = q3.id
    return replace(v, tip=tip, finalized=q3.id)


def check_vote_slot(v, vote):
    """Allow one signed action per exact Block, plus exact replay."""
    v = evidence_source(v)
    old = next((old for old in v.votes
                if (old.signer, old.chain, old.target) ==
                   (vote.signer, vote.chain, vote.target)), None)
    require(old is None or old == vote, 'double vote for exact Block')


def check_vote_target(target, vote):
    """Target-bound header check; dependency walks do not recheck stake."""
    require(vote.chain == target.state.chain and vote.height == target.height + 1 and
            vote.proposer == target.proposer and vote.prev_vote ==
            (target.proposer_vote.inner_id if target.proposer_vote else None),
            'wrong Vote position')


def validate_vote_position(target, vote):
    """Validate target-bound fields and historical stake before history traversal."""
    check_vote_target(target, vote)
    require(vote.stake > 0 and vote.stake == target.state.stake(vote.signer),
            'wrong stake')


def validate_vote_authentication(v, vote, *, allow_evidence_target=False):
    """Validate the authenticated Vote context before history-policy vetoes.

    Exact-Block occupancy and target direction are deliberately excluded. A signed
    action may violate either rule and thereby prove a direct conflict, but a
    malformed position, stake, predecessor, identity, or supplied proof must
    never enter the evidence-only resolver.  This matches the authenticated
    checkpoint that a future Go port must retain.
    """
    source = evidence_source(v)
    collision = next((old for old in source.votes if old.id == vote.id), None)
    require(collision is None or collision == vote, 'Vote identity collision')
    target = (source if allow_evidence_target else v).block(vote.target)
    validate_vote_position(target, vote)
    for old in source.votes:
        if old.inner == vote.inner:
            require((old.inner_id, old.race, old.sig_hash) ==
                    (vote.inner_id, vote.race, vote.sig_hash), 'inner Vote changed')
        else:
            require(old.inner_id != vote.inner_id, 'inner identity collision')
    if vote.prev_self is not None:
        previous = source.vote(vote.prev_self)
        require((previous.signer, previous.chain) == (vote.signer, vote.chain),
                'wrong predecessor signer or chain')
    for proof in vote.exclusions:
        verify_evidence(source, proof)
    require(vote.exclusions == canonical_evidence(source, vote.exclusions),
            'noncanonical Vote exclusion evidence')
    return source


def validate_vote(v, vote, *, allow_evidence_target=False):
    """Validate one Vote with side history available only as a resolver."""
    # Evidence-only objects are historical resolvers, never live inventory.
    source = validate_vote_authentication(
        v, vote, allow_evidence_target=allow_evidence_target)
    check_vote_slot(source, vote)
    if vote.prev_self is not None:
        require(self_segment_active(source, source.vote(vote.prev_self), vote.target),
                'retired self-vote segment requires blank predecessor')
    # Resolve historical duties even when the supplied evidence is empty.
    required_exclusions(source, vote)
    classify_vote_action(
        source, vote, vote.exclusions,
        ordinary_view=source if allow_evidence_target else v)


def validate_evidence_vote(v, vote):
    """Validate a dependency whose authenticated target is evidence-only."""
    validate_vote(v, vote, allow_evidence_target=True)
    return True


def submit_vote(v, vote):
    old = next((old for old in v.votes if old.id == vote.id), None)
    if old is not None:
        require(old == vote, 'Vote identity collision')
        return v
    # A live submission must name a live target even when its signed envelope
    # is also retained in the evidence resolver.  Resolve that boundary first
    # so evidence-only targets remain an availability error, then preserve the
    # model's public admission precedence: an occupied exact Block is
    # reported before deeper envelope authentication.  The owner ingress path
    # authenticates first when deciding whether a rejected action is safe to
    # retain as evidence, so this ordering does not let a malformed conflict
    # enter the evidence-only resolver.
    target = v.block(vote.target)
    validate_vote_position(target, vote)
    check_vote_slot(v, vote)
    # Go still needs this live/resolver split. Validation may read side history,
    # but a new Vote's target must be an admitted live Block.
    validate_vote(v, vote)
    if any(old.id == vote.id for old in v.evidence_votes):
        raise ModelError('evidence-only Vote cannot become live')
    return replace(v, votes=(vote,) + v.votes)


def generate_vote(v, target_id, id, race, sig_hash):
    require_finalized_lineage(v, target_id)
    vote = prospective_vote(v, target_id, id, race, sig_hash)
    old = next((old for old in v.votes if old.inner == vote.inner), None)
    if old is not None:
        require(old.race == race, 'cannot choose another race for the same inner Vote')
        require(old.sig_hash == sig_hash, 'cannot choose another signature hash for the same inner Vote')
        vote = replace(vote, inner_id=old.inner_id)
    require(v.identity not in {e.offender for e in vote.exclusions}, 'excluded local signer')
    admitted = submit_vote(v, vote)
    staged = advance_coverage(replace(admitted, latest=vote.id), target_id)
    require_finalized_lineage(staged, target_id)
    return replace(staged, latest=vote.id, emitted=(vote,) + v.emitted), vote


# Proposal admission and local generation. Parent authority admits the carrier;
# carried evidence computes only the child's output authority.
def stage_block(v, b):
    old = next((old for old in v.blocks if old.id == b.id), None)
    if old is not None:
        require(old == b, 'Block identity collision')
        return v
    side = next((old for old in v.evidence_blocks if old.id == b.id), None)
    if side is not None:
        require(side == b, 'Block identity collision')
        raise ModelError('evidence-only Block cannot become live')
    require(b.parent is not None, 'live Block has no parent')
    parent = v.block(b.parent)
    anchor = historical_q3(v, parent.id).block
    require((b.settled if b.settled is not None else v.ancestry(parent.id)[0].id)
            == anchor.id, 'incorrect finalized prefix')
    require(b.height == parent.height + 1, 'wrong Block height')
    require(b.proposer_vote is not None, 'missing proposer Vote')
    require(all(vote.target == b.parent for vote in b.endorsements),
            'endorsement does not target parent')
    parent_votes = b.endorsements
    require(b.proposer_vote.signer == b.proposer and b.proposer_vote in parent_votes,
            'proposer Vote not in admission batch')
    require(len({vote.signer for vote in parent_votes}) == len(parent_votes),
            'duplicate admission signer')
    staged = v
    for vote in parent_votes:
        staged = submit_vote(staged, vote)
    require(b.exclusions == block_exclusions(staged, b), 'incorrect Block exclusions')
    output_authority = authority_after_evidence(
        staged, parent.id, tuple(record.proof for record in b.exclusions))
    require(b.state == output_authority, 'incorrect authority state')
    admission_authority = parent.state
    require(admission_authority.stake(b.proposer) > 0, 'excluded proposer')
    require(admission_authority.admits(sum(
        admission_authority.stake(vote.signer)
        for vote in parent_votes)),
            'insufficient endorsement stake')
    check_block_improvement(v, b)
    return replace(staged, blocks=(b,) + staged.blocks)


def submit_proposal(v, b, self_vote):
    staged = stage_block(v, b)
    require(self_vote.target == b.id and self_vote.signer == b.proposer,
            'detached self-vote does not bind candidate and proposer')
    staged = submit_vote(staged, self_vote)
    if not actionable(staged, b.id):
        return staged
    return advance_coverage(staged, b.id)


def build_proposal(v, parent_id, own, votes, block_id):
    """Build and validate the normal admission candidate.

    Every available verified proof is carried, including proofs from another
    fork. The carried proof immediately changes this child's authority.
    """
    for vote in votes:
        v = submit_vote(v, vote)
    parent = v.block(parent_id)
    b = Block(block_id, parent_id, parent.height + 1, v.identity, own, votes,
              parent.state)
    anchor = historical_q3(v, parent_id).block
    b = replace(b, settled=anchor.id if anchor.parent is not None else None)
    b = replace(b, exclusions=tuple(
        RecordedExclusion(proof, b.height) for proof in view_evidence(v)))
    b = replace(b, exclusions=block_exclusions(v, b))
    b = replace(b, state=authority_after_evidence(v, parent_id,
                tuple(record.proof for record in b.exclusions)))
    stage_block(v, b)
    return b


def generate_proposal(v, parent_id, block_id, self_vote_id, race, sig_hash):
    require_finalized_lineage(v, parent_id)
    require(v.latest is not None, 'proposal requires a local Vote')
    require(v.vote(v.latest).target == parent_id, 'parent is not latest Vote target')
    require(not any(b.id == block_id for b in v.blocks), 'Block identity already used')
    own = next((vote for vote in v.self_branch(v.latest)
                if vote in v.votes and vote.target == parent_id and
                vote.signer == v.identity), None)
    if own is None:
        raise ModelError('own parent Vote unavailable')
    selected = {v.identity: own}
    for vote in sorted(v.votes, key=lambda vote: (vote.signer, vote.id)):
        if vote.target == parent_id:
            selected.setdefault(vote.signer, vote)
    votes = tuple(selected[signer] for signer in sorted(selected))
    b = build_proposal(v, parent_id, own, votes, block_id)
    staged = stage_block(v, b)
    _, self_vote = generate_vote(staged, b.id, self_vote_id, race, sig_hash)
    signed = replace(submit_vote(staged, self_vote), latest=self_vote.id)
    next_v = submit_proposal(signed, b, self_vote)
    return replace(next_v, latest=self_vote.id, emitted=(self_vote,) + v.emitted), b, self_vote
