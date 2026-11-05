"""Pure quorum and frontier scans over one newest-first ancestry."""

from dataclasses import dataclass

from primitives import Block, require


def has_quorum(state, signers):
    return 3 * sum(state.stake(who) for who in set(signers)) > 2 * state.total


@dataclass(frozen=True)
class QuorumHit:
    block: Block
    older: tuple[Block, ...]
    contributors: frozenset[int]


def support_view(path):
    """Credit every validated endorsement under its target's recorded state.

    Evidence in a carrier changes only that carrier's output state. It cannot
    revoke an endorsement that was valid in the parent state it targets.
    """
    support = {}
    for block in path:
        for vote in block.endorsements:
            support.setdefault(vote.target, set()).add(vote.signer)
    return support


def scan_quorum(path, anchor=None, support=None):
    """Find the newest supported block in a newest-first ancestry.

    A carrier supplies votes for its parent. Each parent is judged under its
    own immutable authority, before evidence changes the carrier's output.
    """
    seen = set()
    if support is None:
        support = support_view(path)
    if anchor is not None and path and path[0].height <= anchor.height:
        return QuorumHit(anchor, path[1:], frozenset())
    for index, (_carrier, candidate) in enumerate(zip(path, path[1:])):
        if anchor is not None and candidate.height <= anchor.height:
            return QuorumHit(anchor, path[index + 2 :], frozenset())
        seen.update(support.get(candidate.id, set()))
        if has_quorum(candidate.state, seen):
            return QuorumHit(candidate, path[index + 2 :], frozenset(seen))
    return None


def frontier(path, anchor=None, support=None):
    hit = scan_quorum(path, anchor, support)
    if hit is not None:
        return hit
    require(path and path[-1].parent is None, "missing Genesis frontier")
    return QuorumHit(path[-1], (), frozenset())
