import Protocol

/-!
# Exact first-divergence ranking

Descendants beat their prefixes. Incomparable chains are decided once, at
their first divergent Blocks, using proposer score and then Block identity.
-/

namespace BFT

/-- `.lt` means the left Block wins. Higher score wins; smaller ID breaks ties. -/
def compareBlocks (left right : Block) : Ordering :=
  if left.proposerVote.score > right.proposerVote.score then .lt
  else if left.proposerVote.score < right.proposerVote.score then .gt
  else compare left.id right.id

/-- Compare exact root-to-tip paths. Later descendants cannot alter a divergence. -/
def compareChains : Chain → Chain → Ordering
  | [], [] => .eq
  | [], _ :: _ => .gt
  | _ :: _, [] => .lt
  | left :: leftTail, right :: rightTail =>
      if left.id = right.id then compareChains leftTail rightTail
      else compareBlocks left right

def Better (left right : Chain) : Prop := compareChains left right = .lt

@[simp] theorem compareBlocks_self (block : Block) : compareBlocks block block = .eq := by
  simp [compareBlocks]

@[simp] theorem compareChains_self (chain : Chain) : compareChains chain chain = .eq := by
  induction chain with
  | nil => rfl
  | cons block tail ih => simp [compareChains, ih]

theorem compareChains_commonPrefix (shared left right : Chain) :
    compareChains (shared ++ left) (shared ++ right) = compareChains left right := by
  induction shared with
  | nil => rfl
  | cons block tail ih => simp [compareChains, ih]

theorem compareChains_firstDivergence
    (shared leftTail rightTail : Chain) (left right : Block)
    (different : left.id ≠ right.id) :
    compareChains (shared ++ left :: leftTail) (shared ++ right :: rightTail) =
      compareBlocks left right := by
  rw [compareChains_commonPrefix]
  simp [compareChains, different]

theorem compareChains_descendant (shared suffix : Chain) (nonempty : suffix ≠ []) :
    compareChains (shared ++ suffix) shared = .lt := by
  calc
    compareChains (shared ++ suffix) shared = compareChains suffix [] := by
      simpa using compareChains_commonPrefix shared suffix []
    _ = .lt := by
      cases suffix with
      | nil => exact (nonempty rfl).elim
      | cons block tail => rfl

theorem compareChains_prefix_loses (shared suffix : Chain) (nonempty : suffix ≠ []) :
    compareChains shared (shared ++ suffix) = .gt := by
  calc
    compareChains shared (shared ++ suffix) = compareChains [] suffix := by
      simpa using compareChains_commonPrefix shared [] suffix
    _ = .gt := by
      cases suffix with
      | nil => exact (nonempty rfl).elim
      | cons block tail => rfl

theorem compareBlocks_sameProposal_scoreTie
    (left right : Block) (_same : left.sameProposal right)
    (sameScore : left.proposerVote.score = right.proposerVote.score) :
    compareBlocks left right = compare left.id right.id := by
  simp [compareBlocks, sameScore]

theorem compareBlocks_sameProposal_smallerHash
    (left right : Block) (same : left.sameProposal right)
    (sameScore : left.proposerVote.score = right.proposerVote.score)
    (smaller : left.id < right.id) : compareBlocks left right = .lt := by
  rw [compareBlocks_sameProposal_scoreTie left right same sameScore]
  exact Nat.compare_eq_lt.mpr smaller

theorem laterDescendants_doNotChangeWinner
    (shared leftTail rightTail leftMore rightMore : Chain)
    (left right : Block) (different : left.id ≠ right.id) :
    compareChains (shared ++ left :: (leftTail ++ leftMore))
        (shared ++ right :: (rightTail ++ rightMore)) =
      compareChains (shared ++ left :: leftTail) (shared ++ right :: rightTail) := by
  rw [compareChains_firstDivergence shared (leftTail ++ leftMore)
      (rightTail ++ rightMore) left right different]
  rw [compareChains_firstDivergence shared leftTail rightTail left right different]

end BFT
