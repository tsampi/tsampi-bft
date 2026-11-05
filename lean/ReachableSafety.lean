import CatchupSafety

/-!
# Reachable consensus safety

This layer records the protocol state that matters to agreement: durable Vote
emissions and completed quorum certificates. Receiving other objects is a
stuttering step. Every emitted honest Vote must pass one of the three
target-transition checks, and every accepted certificate is checked against
the parent authority carried by its target.
-/

namespace BFT

/-- Certificate data independent of the particular event-list snapshot in
which it is stored. -/
structure StoredFinalityLock {α : Type} {system : FrontierSystem α}
    (model : HeightModel system) where
  locked : α
  root : α
  contributors : List (RankedVoteEvent system)
  covers : ∀ event ∈ contributors,
    system.tree.reaches locked event.ranked.q2
  belowRoot : ∀ event ∈ contributors,
    model.height event.ranked.target < model.height root
  parentAuthority : Authority
  authorityEvidence : List CarriedEvidence

def StoredFinalityLock.signers {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} (lock : StoredFinalityLock model) : List ValidatorId :=
  lock.contributors.map RankedVoteEvent.signer

def StoredFinalityLock.toRanked {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} (lock : StoredFinalityLock model)
    {events : List (RankedVoteEvent system)}
    (stored : ∀ event ∈ lock.contributors, event ∈ events) :
    RankedFinalityLock model events where
  locked := lock.locked
  root := lock.root
  contributors := lock.contributors
  stored := stored
  covers := lock.covers
  belowRoot := lock.belowRoot

/-- All checks performed when a receiver accepts a completed certificate. -/
structure StoredFinalityLock.ValidIn {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} (authority : Authority) (honest : List ValidatorId)
    (events : List (RankedVoteEvent system)) (lock : StoredFinalityLock model) : Prop where
  stored : ∀ event ∈ lock.contributors, event ∈ events
  parentFromRoot : lock.parentAuthority =
    authority.afterEvidence lock.authorityEvidence
  evidenceSafe : ∀ item ∈ lock.authorityEvidence,
    item.proof.offender ∉ honest
  quorum : lock.parentAuthority.hasQuorum lock.signers = true

/-- One admitted carrier and its output authority. Admission is measured by
the immutable parent; carried evidence determines only the child authority. -/
structure CarrierAuthorityTransition where
  step : AuthorityStep
  signers : List ValidatorId
  parentEvidence : List CarriedEvidence
  admittedByParent : step.admitsCarrier signers = true

theorem CarrierAuthorityTransition.child_eq_afterEvidence
    (transition : CarrierAuthorityTransition) :
    transition.step.child =
      transition.step.parent.afterEvidence transition.step.evidence :=
  transition.step.childFromEvidence

theorem CarrierAuthorityTransition.admission_usesParent
    (transition : CarrierAuthorityTransition) :
    transition.step.parent.hasQuorum transition.signers = true :=
  transition.admittedByParent

/-- A recorded carrier starts from a parent authority derived from the common
root, and neither earlier nor newly carried evidence removes an honest signer. -/
structure CarrierAuthorityTransition.ValidFrom
    (transition : CarrierAuthorityTransition)
    (root : Authority) (honest : List ValidatorId) : Prop where
  parentFromRoot : transition.step.parent =
    root.afterEvidence transition.parentEvidence
  parentEvidenceSafe : ∀ item ∈ transition.parentEvidence,
    item.proof.offender ∉ honest
  evidenceSafe : ∀ item ∈ transition.step.evidence,
    item.proof.offender ∉ honest

theorem CarrierAuthorityTransition.ValidFrom.childFromRoot
    {transition : CarrierAuthorityTransition}
    {root : Authority} {honest : List ValidatorId}
    (valid : transition.ValidFrom root honest) :
    transition.step.child = root.afterEvidence
      (transition.parentEvidence ++ transition.step.evidence) := by
  calc
    transition.step.child =
        transition.step.parent.afterEvidence transition.step.evidence :=
      transition.child_eq_afterEvidence
    _ = (root.afterEvidence transition.parentEvidence).afterEvidence
        transition.step.evidence := by rw [valid.parentFromRoot]
    _ = root.afterEvidence
        (transition.parentEvidence ++ transition.step.evidence) :=
      Authority.afterEvidence_append root transition.parentEvidence
        transition.step.evidence

structure ProtocolState {α : Type} (system : FrontierSystem α)
    (model : HeightModel system) where
  events : List (RankedVoteEvent system)
  locks : List (StoredFinalityLock model)
  authorityTransitions : List CarrierAuthorityTransition

def ProtocolState.genesis {α : Type} {system : FrontierSystem α}
    (model : HeightModel system) : ProtocolState system model :=
  { events := [], locks := [], authorityTransitions := [] }

/-- Safety-relevant protocol transition. Block and Vote receipts that do not
add a durable Vote emission or certificate use `stutter`. -/
inductive ProtocolStep {α : Type} {system : FrontierSystem α}
    (model : HeightModel system) (authority : Authority) (honest : List ValidatorId) :
    ProtocolState system model → ProtocolState system model → Type
  | stutter (state) : ProtocolStep model authority honest state state
  | admitCertificate {before : ProtocolState system model}
      (lock : StoredFinalityLock model)
      (valid : lock.ValidIn authority honest before.events) :
      ProtocolStep model authority honest before
        { events := before.events
          locks := before.locks ++ [lock]
          authorityTransitions := before.authorityTransitions }
  | emitVote {before : ProtocolState system model}
      (event : RankedVoteEvent system)
      (freshTime : ∀ previous ∈ before.events, previous.time < event.time)
      (freshBlock : ∀ previous ∈ before.events,
        previous.signer = event.signer →
          previous.ranked.target ≠ event.ranked.target)
      (classified : event.signer ∈ honest → ∀ previous ∈ before.events,
        previous.signer = event.signer →
          CertifiedRankTransition model event.ranked previous.ranked)
      (q3Ready : event.ranked.q3 = model.genesis ∨
        ∃ lock ∈ before.locks, lock.locked = event.ranked.q3 ∧
          model.height lock.root ≤ model.height event.ranked.target) :
      ProtocolStep model authority honest before
        { events := before.events ++ [event]
          locks := before.locks
          authorityTransitions := before.authorityTransitions }
  | applyAuthority {before : ProtocolState system model}
      (transition : CarrierAuthorityTransition)
      (valid : transition.ValidFrom authority honest) :
      ProtocolStep model authority honest before
        { events := before.events
          locks := before.locks
          authorityTransitions := before.authorityTransitions ++ [transition] }

inductive ReachableConsensus {α : Type} {system : FrontierSystem α}
    (model : HeightModel system) (authority : Authority) (honest : List ValidatorId) :
    ProtocolState system model → Prop
  | genesis : ReachableConsensus model authority honest (ProtocolState.genesis model)
  | step {before after} :
      ReachableConsensus model authority honest before →
      ProtocolStep model authority honest before after →
      ReachableConsensus model authority honest after

/-- Invariants derived from the transition relation rather than supplied to
the final safety theorem. -/
structure ProtocolState.Consistent {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} (authority : Authority) (honest : List ValidatorId)
    (state : ProtocolState system model) : Prop where
  history : CertifiedRankHistory model (fun signer ↦ signer ∈ honest) state.events
  validLocks : ∀ lock ∈ state.locks, lock.ValidIn authority honest state.events
  q3Covered : ∀ event ∈ state.events, event.ranked.q3 ≠ model.genesis →
    ∃ lock ∈ state.locks, lock.locked = event.ranked.q3 ∧
      model.height lock.root ≤ model.height event.ranked.target
  validAuthorities : ∀ transition ∈ state.authorityTransitions,
    transition.ValidFrom authority honest

def ProtocolState.AcceptedLock {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} (state : ProtocolState system model)
    (lock : RankedFinalityLock model state.events) : Prop :=
  ∃ raw ∈ state.locks, ∃ stored,
    lock = raw.toRanked stored

def ProtocolState.Finalized {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} (state : ProtocolState system model) (block : α) : Prop :=
  block = model.genesis ∨ ∃ lock ∈ state.locks, lock.locked = block

theorem StoredFinalityLock.ValidIn.monoEvents {α : Type}
    {system : FrontierSystem α} {model : HeightModel system}
    {authority : Authority} {honest : List ValidatorId}
    {older newer : List (RankedVoteEvent system)} {lock : StoredFinalityLock model}
    (valid : lock.ValidIn authority honest older)
    (subset : ∀ event ∈ older, event ∈ newer) :
    lock.ValidIn authority honest newer := by
  exact {
    stored := fun event member ↦ subset event (valid.stored event member)
    parentFromRoot := valid.parentFromRoot
    evidenceSafe := valid.evidenceSafe
    quorum := valid.quorum
  }

theorem ProtocolStep.preserveConsistency {α : Type}
    {system : FrontierSystem α} {model : HeightModel system}
    {authority : Authority} {honest : List ValidatorId}
    {before after : ProtocolState system model}
    (step : ProtocolStep model authority honest before after)
    (consistent : before.Consistent authority honest) :
    after.Consistent authority honest := by
  cases step with
  | stutter => exact consistent
  | admitCertificate lock valid =>
      refine ⟨consistent.history, ?_, ?_, consistent.validAuthorities⟩
      · intro candidate member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with old | added
        · exact consistent.validLocks candidate old
        · subst candidate
          exact valid
      · intro event member nonGenesis
        obtain ⟨candidate, stored, locked, bound⟩ :=
          consistent.q3Covered event member nonGenesis
        exact ⟨candidate, List.mem_append_left [lock] stored, locked, bound⟩
  | emitVote event freshTime _ classified q3Ready =>
      refine ⟨?_, ?_, ?_, consistent.validAuthorities⟩
      · let signingBefore : RankedSigningState system := { events := before.events }
        let signingAfter : RankedSigningState system :=
          { events := before.events ++ [event] }
        have signingStep : CertifiedSigningStep model
            (fun signer ↦ signer ∈ honest) signingBefore signingAfter := {
          event := event
          freshTime := freshTime
          classified := classified
          appended := rfl
        }
        exact signingStep.preserveHistory consistent.history
      · intro lock member
        apply (consistent.validLocks lock member).monoEvents
        intro previous previousMember
        exact List.mem_append_left [event] previousMember
      · intro candidate member nonGenesis
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with old | added
        · exact consistent.q3Covered candidate old nonGenesis
        · subst candidate
          rcases q3Ready with atGenesis | ready
          · exact (nonGenesis atGenesis).elim
          · exact ready
  | applyAuthority transition valid =>
      refine ⟨consistent.history, consistent.validLocks, consistent.q3Covered, ?_⟩
      intro candidate member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with old | added
      · exact consistent.validAuthorities candidate old
      · subst candidate
        exact valid

theorem ReachableConsensus.consistent {α : Type}
    {system : FrontierSystem α} {model : HeightModel system}
    {authority : Authority} {honest : List ValidatorId}
    {state : ProtocolState system model}
    (reachable : ReachableConsensus model authority honest state) :
    state.Consistent authority honest := by
  induction reachable with
  | genesis =>
      constructor <;> simp [ProtocolState.genesis, CertifiedRankHistory]
  | step earlier next ih =>
      exact next.preserveConsistency ih

/-- Every pair of finalized Blocks in a reachable state is ancestry-compatible.
The only tree fact supplied separately is that Genesis precedes every Block. -/
theorem ReachableConsensus.finalizedSafety {α : Type}
    {system : FrontierSystem α} {model : HeightModel system}
    {authority : Authority} {honest : List ValidatorId}
    {state : ProtocolState system model}
    (reachable : ReachableConsensus model authority honest state)
    (unique : (authority.members.map Prod.fst).Nodup)
    (honestQuorum : authority.hasQuorum honest = true)
    (genesisBelow : ∀ block, system.tree.reaches model.genesis block)
    {left right : α} (leftFinalized : state.Finalized left)
    (rightFinalized : state.Finalized right) :
    system.tree.reaches left right ∨ system.tree.reaches right left := by
  rcases leftFinalized with leftGenesis | ⟨leftRaw, leftMember, leftLocked⟩
  · subst left
    exact Or.inl (genesisBelow right)
  rcases rightFinalized with rightGenesis | ⟨rightRaw, rightMember, rightLocked⟩
  · subst right
    exact Or.inr (genesisBelow left)
  have consistent := reachable.consistent
  have leftValid := consistent.validLocks leftRaw leftMember
  have rightValid := consistent.validLocks rightRaw rightMember
  let leftLock := leftRaw.toRanked leftValid.stored
  let rightLock := rightRaw.toRanked rightValid.stored
  have agreement := rankedFinalityAgreement_of model
    (fun signer ↦ signer ∈ honest) state.events consistent.history state.AcceptedLock
    (by
      intro first second firstAccepted secondAccepted
      obtain ⟨firstRaw, firstMember, firstStored, firstEqual⟩ := firstAccepted
      obtain ⟨secondRaw, secondMember, secondStored, secondEqual⟩ := secondAccepted
      subst first
      subst second
      have firstValid := consistent.validLocks firstRaw firstMember
      have secondValid := consistent.validLocks secondRaw secondMember
      apply rankedLocks_shareHonest_afterEvidence_both authority honest
        firstRaw.authorityEvidence secondRaw.authorityEvidence
      · exact unique
      · exact firstValid.evidenceSafe
      · exact secondValid.evidenceSafe
      · exact honestQuorum
      · rw [← firstValid.parentFromRoot]
        simpa [StoredFinalityLock.toRanked, RankedFinalityLock.signers,
          StoredFinalityLock.signers] using
          firstValid.quorum
      · rw [← secondValid.parentFromRoot]
        simpa [StoredFinalityLock.toRanked, RankedFinalityLock.signers,
          StoredFinalityLock.signers] using
          secondValid.quorum)
    (by
      intro event eventMember nonGenesis
      obtain ⟨raw, rawMember, locked, bound⟩ :=
        consistent.q3Covered event eventMember nonGenesis
      have valid := consistent.validLocks raw rawMember
      let lock := raw.toRanked valid.stored
      exact ⟨lock, ⟨raw, rawMember, valid.stored, rfl⟩, locked, bound⟩)
    leftLock rightLock
    ⟨leftRaw, leftMember, leftValid.stored, rfl⟩
    ⟨rightRaw, rightMember, rightValid.stored, rfl⟩
  simpa [leftLock, rightLock, StoredFinalityLock.toRanked, leftLocked,
    rightLocked] using agreement

end BFT
