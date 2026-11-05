import Ranking

/-!
# Finite delivery and quorum scanning

This module contains the finite candidate-delivery boundary and the exact
newest-first quorum scan shared by the protocol liveness proof and parity
adapter. The protocol-state liveness theorem is in `ProtocolLiveness`.
-/

namespace BFT

def selectedCandidate (inventory : List Chain) : Option Chain :=
  inventory.head?

theorem sameFiniteInventory_converges (leftInventory rightInventory : List Chain)
    (delivered : leftInventory = rightInventory) :
    selectedCandidate leftInventory = selectedCandidate rightInventory := by
  rw [delivered]

theorem selectedCandidate_exists (inventory : List Chain) (nonempty : inventory ≠ []) :
    ∃ selected, selectedCandidate inventory = some selected := by
  cases inventory with
  | nil => exact (nonempty rfl).elim
  | cons first rest => exact ⟨first, rfl⟩

structure EventualDelivery (honest : List ValidatorId)
    (observed : ValidatorId → List Chain) (inventory : List Chain) : Prop where
  delivered : ∀ validator ∈ honest, observed validator = inventory

theorem EventualDelivery.converges {honest : List ValidatorId}
    {observed : ValidatorId → List Chain} {inventory : List Chain}
    (delivery : EventualDelivery honest observed inventory) :
    ∀ validator ∈ honest,
      selectedCandidate (observed validator) = selectedCandidate inventory := by
  intro validator member
  rw [delivery.delivered validator member]

structure CanonicalInventory (validCandidate : Chain → Prop) where
  candidates : List Chain
  selected : Chain
  selectedAtHead : selectedCandidate candidates = some selected
  selectedValid : validCandidate selected
  selectedBest : ∀ candidate ∈ candidates,
    compareChains selected candidate ≠ .gt

/-- A target and the parent endorsements carried by each later child. This is
the finite scan representation used by the parity adapter. -/
inductive ScannedTarget
  | base (target : Chain) (authority : Authority)
  | child (parent : ScannedTarget) (target : Chain)
      (signers : List ValidatorId) (evidence : List CarriedEvidence)

def ScannedTarget.target : ScannedTarget → Chain
  | .base target _ => target
  | .child _ target _ _ => target

/-- Evidence in a carrier changes its output authority, never its parent's. -/
def ScannedTarget.authority : ScannedTarget → Authority
  | .base _ authority => authority
  | .child parent _ _ evidence => parent.authority.afterEvidence evidence

/-- The cumulative newest-first quorum scan, stopped at the chosen base. -/
def ScannedTarget.scan : ScannedTarget → List ValidatorId → ScannedTarget
  | .base target authority, _ => .base target authority
  | .child parent _ signers _, seen =>
      let combined := seen ++ signers
      if parent.authority.hasQuorum combined then parent
      else parent.scan combined

def ScannedTarget.q1 (target : ScannedTarget) : ScannedTarget :=
  target.scan []

def ScannedTarget.q2 (target : ScannedTarget) : ScannedTarget :=
  target.q1.q1

def ScannedTarget.q3 (target : ScannedTarget) : ScannedTarget :=
  target.q2.q1

@[simp] theorem ScannedTarget.child_authority
    (parent : ScannedTarget) (target : Chain)
    (signers : List ValidatorId) (evidence : List CarriedEvidence) :
    (ScannedTarget.child parent target signers evidence).authority =
      parent.authority.afterEvidence evidence := rfl

theorem ScannedTarget.child_q1_of_parent_quorum
    (parent : ScannedTarget) (target : Chain)
    (signers : List ValidatorId) (evidence : List CarriedEvidence)
    (quorum : parent.authority.hasQuorum signers = true) :
    (ScannedTarget.child parent target signers evidence).q1 = parent := by
  simp [ScannedTarget.q1, ScannedTarget.scan, quorum]

/-- Prefix ancestry used by the concrete nonvacuity witness. -/
def prefixChainTree : Ancestry Chain where
  reaches := List.IsPrefix
  refl := List.prefix_refl
  trans := List.IsPrefix.trans
  ancestorsComparable := List.prefix_or_prefix_of_prefix

end BFT
