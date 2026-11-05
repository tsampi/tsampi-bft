import Protocol

/-!
# The safety content of ordinary target switching

`proposal_improves` computes nested Q1 frontiers.  Its ranking details decide
which safe candidate wins; safety needs only the guard facts below.  The three
ranking guards preserve Q2. Certified catch-up is handled once, with its height
bound and certificate argument, in `CatchupSafety`.
-/

namespace BFT

/-- A historical Q1 query on one immutable ancestry tree. -/
structure FrontierSystem (α : Type) where
  tree : Ancestry α
  frontier : α → α
  frontierBelow : ∀ target, tree.reaches (frontier target) target
  frontierMonotone : ∀ {previous current}, tree.reaches previous current →
    tree.reaches (frontier previous) (frontier current)

/-- A target together with its Q1/Q2/Q3 values, computed by iteration. -/
structure RankedTarget {α : Type} (system : FrontierSystem α) where
  target : α

def RankedTarget.q1 {α : Type} {system : FrontierSystem α}
    (ranked : RankedTarget system) : α :=
  system.frontier ranked.target

def RankedTarget.q2 {α : Type} {system : FrontierSystem α}
    (ranked : RankedTarget system) : α :=
  system.frontier ranked.q1

def RankedTarget.q3 {α : Type} {system : FrontierSystem α}
    (ranked : RankedTarget system) : α :=
  system.frontier ranked.q2

/-- The ancestry checks used by the scored and one-sided proposal guards.
The score/hash comparison chooses a direction but contributes no lock fact. -/
def ProposalGuard {α : Type} (system : FrontierSystem α)
    (current previous : RankedTarget system) : Prop :=
  system.tree.reaches previous.q1 current.q1 ∨
  system.tree.reaches previous.q2 current.q2 ∨
  (system.tree.reaches previous.q2 current.q1 ∧
    ¬(previous.q1 ≠ current.q2 ∧
      system.tree.reaches current.q2 previous.q1))

theorem proposalGuard_preservesQ2 {α : Type} {system : FrontierSystem α}
    {current previous : RankedTarget system}
    (guard : ProposalGuard system current previous) :
    system.tree.reaches previous.q2 current.q2 := by
  rcases guard with q1Nonretreating | q2Nonretreating | oneSided
  · exact system.frontierMonotone q1Nonretreating
  · exact q2Nonretreating
  · rcases oneSided with ⟨previousQ2BelowCurrentQ1, noReverseDescent⟩
    have currentQ2BelowCurrentQ1 := system.frontierBelow current.q1
    rcases system.tree.ancestorsComparable currentQ2BelowCurrentQ1
        previousQ2BelowCurrentQ1 with reverse | forward
    · by_cases boundary : previous.q1 = current.q2
      · change system.tree.reaches (system.frontier previous.q1) current.q2
        rw [← boundary]
        exact system.frontierBelow previous.q1
      · have reverseToPreviousQ1 :=
          system.tree.trans reverse (system.frontierBelow previous.q1)
        exact False.elim (noReverseDescent ⟨boundary, reverseToPreviousQ1⟩)
    · exact forward

end BFT
