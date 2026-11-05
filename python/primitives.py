"""Immutable protocol objects shared by the executable consensus rules."""

from dataclasses import dataclass, replace


class ModelError(ValueError):
    """Invalid input or an unavailable dependency (kind, object_id)."""

    def __init__(self, reason, kind="invalid", object_id=None):
        super().__init__(reason)
        self.kind, self.object_id = kind, object_id


def require(condition, reason):
    if not condition:
        raise ModelError(reason)


@dataclass(frozen=True)
class State:
    chain: int
    members: tuple[tuple[int, int], ...]
    numerator: int
    denominator: int

    def stake(self, identity):
        return next((weight for who, weight in self.members if who == identity), 0)

    @property
    def total(self):
        return sum(weight for _, weight in self.members)

    def admits(self, weight):
        if self.numerator == self.denominator:
            return weight == self.total
        return weight * self.denominator > self.total * self.numerator

    def without(self, offenders):
        excluded = set(offenders)
        members = tuple(
            (who, weight) for who, weight in self.members if who not in excluded
        )
        require(bool(members), "empty authority state")
        return replace(self, members=members)


@dataclass(frozen=True)
class Evidence:
    offender: int
    votes: tuple[int, ...]  # Two conflicting Votes, or one signed accounting violation.
    causes: tuple["Evidence", ...] = ()
    duty_floor: int = 0  # Inclusive finalized floor of a derived accounting query.


@dataclass(frozen=True)
class RecordedExclusion:
    proof: Evidence
    recorded_height: int  # First recording on this exact Block lineage.

    @property
    def offender(self):
        return self.proof.offender


@dataclass(frozen=True)
class Vote:
    id: int
    inner_id: int
    signer: int
    chain: int
    height: int
    proposer: int
    prev_vote: int | None
    target: int
    stake: int
    prev_self: int | None
    race: int
    sig_hash: int
    exclusions: tuple[Evidence, ...] = ()

    @property
    def inner(self):
        return self.signer, self.chain, self.height, self.proposer, self.prev_vote


@dataclass(frozen=True)
class Block:
    id: int
    parent: int | None
    height: int
    proposer: int
    proposer_vote: Vote | None
    endorsements: tuple[Vote, ...]  # Role is derived from each Vote's target.
    state: State
    exclusions: tuple[RecordedExclusion, ...] = ()
    settled: int | None = None  # Immutable parent Q3 scan anchor; None = Genesis.

    @classmethod
    def genesis(cls, id, state):
        return cls(id, None, 0, 0, None, (), state)
