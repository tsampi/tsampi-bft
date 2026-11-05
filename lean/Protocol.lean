import Std

/-!
# Minimal protocol vocabulary

The proof model uses symbolic identities and already-computed proposer scores.
Hashes, signatures, execution, networking, and persistence stay outside Lean.
-/

namespace BFT

abbrev ValidatorId := Nat
abbrev BlockId := Nat
abbrev ProposalPosition := Nat
abbrev Score := Nat
abbrev Stake := Nat

/-- Abstract ancestry supplied by the concrete Block store. -/
structure Ancestry (α : Type) where
  reaches : α → α → Prop
  refl : ∀ block, reaches block block
  trans : ∀ {first second third}, reaches first second → reaches second third →
    reaches first third
  ancestorsComparable : ∀ {left right tip}, reaches left tip → reaches right tip →
    reaches left right ∨ reaches right left

/-- The stable proposer-race value attached to a proposal opportunity. -/
structure ProposerVote where
  signer : ValidatorId
  position : ProposalPosition
  score : Score
  deriving DecidableEq, Repr

/-- Only fields used by ancestry ranking belong in the proof model. -/
structure Block where
  id : BlockId
  proposerVote : ProposerVote
  deriving DecidableEq, Repr

/-- Exact ancestry from genesis to a candidate tip. -/
abbrev Chain := List Block

/-- Two Blocks came from the same proposer opportunity. -/
def Block.sameProposal (left right : Block) : Prop :=
  left.proposerVote.signer = right.proposerVote.signer ∧
    left.proposerVote.position = right.proposerVote.position

/-- Direct equivocation evidence. It records guilt but does not rank Blocks. -/
structure Evidence where
  offender : ValidatorId
  left : BlockId
  right : BlockId
  distinct : left ≠ right

/-- Verified evidence carried by a Block changes that Block's output authority. -/
structure CarriedEvidence where
  carrier : BlockId
  proof : Evidence

/-- Finite authority recorded by a Block. -/
structure Authority where
  members : List (ValidatorId × Stake)
  deriving DecidableEq, Repr

def Authority.weight (authority : Authority) (validator : ValidatorId) : Stake :=
  ((authority.members.find? fun member ↦ member.1 == validator).map Prod.snd).getD 0

def Authority.total (authority : Authority) : Stake :=
  (authority.members.map Prod.snd).sum

def Authority.supportWeight (authority : Authority) (signers : List ValidatorId) : Stake :=
  (signers.eraseDups.map authority.weight).sum

/-- Strict two-thirds quorum used by the protocol. -/
def Authority.hasQuorum (authority : Authority) (signers : List ValidatorId) : Bool :=
  3 * authority.supportWeight signers > 2 * authority.total

def retainedAfterEvidence (evidence : List CarriedEvidence)
    (validator : ValidatorId) : Bool :=
  !evidence.any (fun item ↦ item.proof.offender = validator)

/-! The parent authority admits the carrier; this is the carrier's output state. -/
def Authority.afterEvidence (authority : Authority)
    (evidence : List CarriedEvidence) : Authority :=
  { authority with members := authority.members.filter fun member ↦
      retainedAfterEvidence evidence member.1 }

theorem retainedAfterEvidence_append (first second : List CarriedEvidence)
    (validator : ValidatorId) :
    retainedAfterEvidence (first ++ second) validator =
      (retainedAfterEvidence first validator &&
        retainedAfterEvidence second validator) := by
  simp [retainedAfterEvidence, List.any_append, Bool.not_or]

theorem Authority.afterEvidence_append (authority : Authority)
    (first second : List CarriedEvidence) :
    (authority.afterEvidence first).afterEvidence second =
      authority.afterEvidence (first ++ second) := by
  cases authority with
  | mk members =>
      simp [Authority.afterEvidence, List.filter_filter,
        retainedAfterEvidence_append, Bool.and_comm]

/-- One Block-state transition. The parent authority admits the carrier;
`child` is the authority recorded by that carrier for future children. -/
structure AuthorityStep where
  parent : Authority
  evidence : List CarriedEvidence
  child : Authority
  childFromEvidence : child = parent.afterEvidence evidence

def AuthorityStep.admitsCarrier (step : AuthorityStep)
    (signers : List ValidatorId) : Bool :=
  step.parent.hasQuorum signers

def AuthorityStep.admitsChild (step : AuthorityStep)
    (signers : List ValidatorId) : Bool :=
  step.child.hasQuorum signers

theorem Authority.afterEvidence_offender_zero
    (authority : Authority) (evidence : List CarriedEvidence)
    (item : CarriedEvidence) (found : item ∈ evidence) :
    (authority.afterEvidence evidence).weight item.proof.offender = 0 := by
  unfold Authority.afterEvidence Authority.weight
  rw [List.find?_eq_none.2]
  · rfl
  · intro member membership same
    have retained := (List.mem_filter.mp membership).2
    have offender : member.1 = item.proof.offender := by simpa using same
    have present : evidence.any (fun proof ↦ proof.proof.offender = member.1) = true := by
      apply List.any_eq_true.mpr
      exact ⟨item, found, by simp [offender]⟩
    simp [retainedAfterEvidence, present] at retained

end BFT
