import Frontiers
import Quorum

/-!
# Certified catch-up safety

This layer contains only the facts needed when a certified Q3 catch-up does
not retain Q2 directly. Agreement follows by induction on certificate-root
height; no recovery transition or implementation state belongs here.
-/

namespace BFT

structure RankedVoteEvent {α : Type} (system : FrontierSystem α) where
  time : Nat
  signer : ValidatorId
  ranked : RankedTarget system

structure RankedSigningState {α : Type} (system : FrontierSystem α) where
  events : List (RankedVoteEvent system)

/-- Heights attached to the same ancestry relation used by the frontier model. -/
structure HeightModel {α : Type} (system : FrontierSystem α) where
  height : α → Nat
  reachesHeight : ∀ {ancestor descendant},
    system.tree.reaches ancestor descendant → height ancestor ≤ height descendant
  sameHeight : ∀ {ancestor descendant},
    system.tree.reaches ancestor descendant → height ancestor = height descendant →
      ancestor = descendant
  genesis : α
  genesisHeight : height genesis = 0
  zeroIsGenesis : ∀ block, height block = 0 → block = genesis

/-- Exact rank relation supplied by ordinary protocol classification: Q2 is
retained, or a certified Q3 reaches the old Q2 height. -/
def CertifiedRankLE {α : Type} {system : FrontierSystem α}
    (model : HeightModel system)
    (older newer : RankedTarget system) : Prop :=
  system.tree.reaches older.q2 newer.q2 ∨
    (system.tree.reaches older.q3 newer.q3 ∧
      model.height older.q2 ≤ model.height newer.q3)

/-- The three target changes admitted by the protocol. The first two retain
Q2; certified catch-up retains Q3 and reaches the old Q2 height. -/
inductive CertifiedRankTransition {α : Type} {system : FrontierSystem α}
    (model : HeightModel system) :
    RankedTarget system → RankedTarget system → Prop
  | descendant {current previous} :
      system.tree.reaches previous.target current.target →
      CertifiedRankTransition model current previous
  | ranked {current previous} :
      ProposalGuard system current previous →
      CertifiedRankTransition model current previous
  | certifiedCatchup {current previous} :
      system.tree.reaches previous.q3 current.q3 →
      model.height previous.q2 ≤ model.height current.q3 →
      CertifiedRankTransition model current previous

theorem CertifiedRankTransition.certifiedRankLE
    {α : Type} {system : FrontierSystem α} {model : HeightModel system}
    {current previous : RankedTarget system}
    (transition : CertifiedRankTransition model current previous) :
    CertifiedRankLE model previous current := by
  cases transition with
  | descendant descent =>
      exact Or.inl (system.frontierMonotone (system.frontierMonotone descent))
  | ranked guard =>
      exact Or.inl (proposalGuard_preservesQ2 guard)
  | certifiedCatchup q3 height =>
      exact Or.inr ⟨q3, height⟩

/-- One completed outer-Q1 certificate. Every counted contributor has a Q2
lock covering `locked`, and signed below the certificate root. -/
structure RankedFinalityLock {α : Type} {system : FrontierSystem α}
    (model : HeightModel system) (events : List (RankedVoteEvent system)) where
  locked : α
  root : α
  contributors : List (RankedVoteEvent system)
  stored : ∀ event ∈ contributors, event ∈ events
  covers : ∀ event ∈ contributors,
    system.tree.reaches locked event.ranked.q2
  belowRoot : ∀ event ∈ contributors,
    model.height event.ranked.target < model.height root

def RankedFinalityLock.signers {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {events : List (RankedVoteEvent system)}
    (lock : RankedFinalityLock model events) : List ValidatorId :=
  lock.contributors.map RankedVoteEvent.signer

def RankedLockOverlap {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {events : List (RankedVoteEvent system)}
    (honest : ValidatorId → Prop)
    (left right : RankedFinalityLock model events) : Prop :=
  ∃ leftEvent ∈ left.contributors, ∃ rightEvent ∈ right.contributors,
    honest leftEvent.signer ∧ leftEvent.signer = rightEvent.signer

theorem rankedLocks_shareHonest_afterEvidence_both
    {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {events : List (RankedVoteEvent system)}
    (authority : Authority) (honest : List ValidatorId)
    (leftEvidence rightEvidence : List CarriedEvidence)
    (left right : RankedFinalityLock model events)
    (unique : (authority.members.map Prod.fst).Nodup)
    (leftSafe : ∀ item ∈ leftEvidence, item.proof.offender ∉ honest)
    (rightSafe : ∀ item ∈ rightEvidence, item.proof.offender ∉ honest)
    (honestQuorum : authority.hasQuorum honest = true)
    (leftQuorum : (authority.afterEvidence leftEvidence).hasQuorum
      left.signers = true)
    (rightQuorum : (authority.afterEvidence rightEvidence).hasQuorum
      right.signers = true) :
    RankedLockOverlap (fun signer ↦ signer ∈ honest) left right := by
  obtain ⟨signer, signerHonest, signerLeft, signerRight⟩ :=
    afterEvidenceQuorums_shareHonest_both authority leftEvidence rightEvidence
      honest left.signers right.signers unique leftSafe rightSafe honestQuorum
      leftQuorum rightQuorum
  obtain ⟨leftEvent, leftMember, leftSigner⟩ := List.mem_map.mp signerLeft
  obtain ⟨rightEvent, rightMember, rightSigner⟩ := List.mem_map.mp signerRight
  have leftHonest : leftEvent.signer ∈ honest := by simpa [leftSigner] using signerHonest
  exact ⟨leftEvent, leftMember, rightEvent, rightMember, leftHonest,
    leftSigner.trans rightSigner.symm⟩

def CertifiedRankHistory {α : Type} {system : FrontierSystem α}
    (model : HeightModel system) (honest : ValidatorId → Prop)
    (events : List (RankedVoteEvent system)) : Prop :=
  ∀ older ∈ events, ∀ newer ∈ events,
    honest older.signer → older.signer = newer.signer → older.time ≤ newer.time →
      CertifiedRankLE model older.ranked newer.ranked

theorem CertifiedRankLE.refl {α : Type} {system : FrontierSystem α}
    (model : HeightModel system) (ranked : RankedTarget system) :
    CertifiedRankLE model ranked ranked :=
  Or.inl (system.tree.refl ranked.q2)

structure CertifiedSigningStep {α : Type} {system : FrontierSystem α}
    (model : HeightModel system) (honest : ValidatorId → Prop)
    (before after : RankedSigningState system) where
  event : RankedVoteEvent system
  freshTime : ∀ previous ∈ before.events, previous.time < event.time
  classified : honest event.signer → ∀ previous ∈ before.events,
    previous.signer = event.signer →
      CertifiedRankTransition model event.ranked previous.ranked
  appended : after.events = before.events ++ [event]

theorem CertifiedSigningStep.preserveHistory
    {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {honest : ValidatorId → Prop}
    {before after : RankedSigningState system}
    (step : CertifiedSigningStep model honest before after)
    (history : CertifiedRankHistory model honest before.events) :
    CertifiedRankHistory model honest after.events := by
  intro older olderMember newer newerMember olderHonest sameSigner timeOrder
  rw [step.appended] at olderMember newerMember
  simp only [List.mem_append, List.mem_singleton] at olderMember newerMember
  rcases olderMember with olderStored | olderNew <;>
    rcases newerMember with newerStored | newerNew
  · exact history older olderStored newer newerStored olderHonest sameSigner timeOrder
  · subst newer
    have eventHonest : honest step.event.signer := by
      simpa [← sameSigner] using olderHonest
    exact (step.classified eventHonest older olderStored sameSigner).certifiedRankLE
  · subst older
    have impossible := step.freshTime newer newerStored
    omega
  · subst older
    subst newer
    exact CertifiedRankLE.refl model step.event.ranked

private theorem rankedFinalityAgreementAux {α : Type} {system : FrontierSystem α}
    (model : HeightModel system) (honest : ValidatorId → Prop)
    (events : List (RankedVoteEvent system))
    (history : CertifiedRankHistory model honest events)
    (accepted : RankedFinalityLock model events → Prop)
    (overlap : ∀ left right : RankedFinalityLock model events,
      accepted left → accepted right → RankedLockOverlap honest left right)
    (q3Lock : ∀ event : RankedVoteEvent system, event ∈ events →
      event.ranked.q3 ≠ model.genesis →
      ∃ lock : RankedFinalityLock model events,
        accepted lock ∧ lock.locked = event.ranked.q3 ∧
          model.height lock.root ≤ model.height event.ranked.target)
    (bound : Nat) (left right : RankedFinalityLock model events)
    (rootBound : model.height left.root + model.height right.root ≤ bound)
    (leftAccepted : accepted left) (rightAccepted : accepted right) :
    system.tree.reaches left.locked right.locked ∨
      system.tree.reaches right.locked left.locked := by
  induction bound using Nat.strongRecOn generalizing left right with
  | ind bound ih =>
    obtain ⟨leftEvent, leftMember, rightEvent, rightMember, leftHonest, sameSigner⟩ :=
      overlap left right leftAccepted rightAccepted
    have compareOrdered {older newer : RankedFinalityLock model events}
        {olderEvent newerEvent : RankedVoteEvent system}
        (pairBound : model.height older.root + model.height newer.root ≤ bound)
        (olderAccepted : accepted older) (newerAccepted : accepted newer)
        (olderMember : olderEvent ∈ older.contributors)
        (newerMember : newerEvent ∈ newer.contributors)
        (olderHonest : honest olderEvent.signer)
        (same : olderEvent.signer = newerEvent.signer)
        (time : olderEvent.time ≤ newerEvent.time) :
        system.tree.reaches older.locked newer.locked ∨
          system.tree.reaches newer.locked older.locked := by
      have ordered := history olderEvent (older.stored olderEvent olderMember)
        newerEvent (newer.stored newerEvent newerMember) olderHonest same time
      rcases ordered with q2Retained | ⟨_, certifiedHeight⟩
      · have olderCovered := system.tree.trans (older.covers olderEvent olderMember) q2Retained
        exact system.tree.ancestorsComparable olderCovered
          (newer.covers newerEvent newerMember)
      · have lockedHeight :
            model.height older.locked ≤ model.height newerEvent.ranked.q3 :=
          Nat.le_trans (model.reachesHeight (older.covers olderEvent olderMember))
            certifiedHeight
        have olderToQ3 : system.tree.reaches older.locked newerEvent.ranked.q3 := by
          by_cases atGenesis : newerEvent.ranked.q3 = model.genesis
          · have lockedZero : model.height older.locked = 0 := by
              apply Nat.eq_zero_of_le_zero
              simpa [atGenesis, model.genesisHeight] using lockedHeight
            have lockedGenesis := model.zeroIsGenesis older.locked lockedZero
            simpa [atGenesis, lockedGenesis] using system.tree.refl model.genesis
          · obtain ⟨pivot, pivotAccepted, pivotLocked, pivotBound⟩ :=
              q3Lock newerEvent (newer.stored newerEvent newerMember) atGenesis
            have newerBelow := newer.belowRoot newerEvent newerMember
            have smaller :
                model.height older.root + model.height pivot.root < bound := by
              omega
            have compared := ih _ smaller older pivot (Nat.le_refl _)
              olderAccepted pivotAccepted
            rcases compared with olderToPivot | pivotToOlder
            · simpa [pivotLocked] using olderToPivot
            · have pivotHeight : model.height pivot.locked ≤ model.height older.locked :=
                model.reachesHeight pivotToOlder
              have olderHeight : model.height older.locked ≤ model.height pivot.locked := by
                simpa [pivotLocked] using lockedHeight
              have sameHeight : model.height pivot.locked = model.height older.locked :=
                Nat.le_antisymm pivotHeight olderHeight
              have sameBlock := model.sameHeight pivotToOlder sameHeight
              simpa [← sameBlock, pivotLocked] using system.tree.refl pivot.locked
        have olderCovered := system.tree.trans olderToQ3
          (system.frontierBelow newerEvent.ranked.q2)
        exact system.tree.ancestorsComparable olderCovered
          (newer.covers newerEvent newerMember)
    rcases Nat.le_total leftEvent.time rightEvent.time with leftFirst | rightFirst
    · exact compareOrdered rootBound leftAccepted rightAccepted leftMember rightMember
        leftHonest sameSigner leftFirst
    · have rightHonest : honest rightEvent.signer := by
        simpa [← sameSigner] using leftHonest
      have reversedBound : model.height right.root + model.height left.root ≤ bound := by
        omega
      exact (compareOrdered reversedBound rightAccepted leftAccepted rightMember leftMember
        rightHonest sameSigner.symm rightFirst).symm

/-- Finality agreement restricted to the certificates accepted by a reachable
protocol state. Recursive Q3 certificates must be accepted by that same state. -/
theorem rankedFinalityAgreement_of {α : Type} {system : FrontierSystem α}
    (model : HeightModel system) (honest : ValidatorId → Prop)
    (events : List (RankedVoteEvent system))
    (history : CertifiedRankHistory model honest events)
    (accepted : RankedFinalityLock model events → Prop)
    (overlap : ∀ left right : RankedFinalityLock model events,
      accepted left → accepted right → RankedLockOverlap honest left right)
    (q3Lock : ∀ event : RankedVoteEvent system, event ∈ events →
      event.ranked.q3 ≠ model.genesis →
      ∃ lock : RankedFinalityLock model events,
        accepted lock ∧ lock.locked = event.ranked.q3 ∧
          model.height lock.root ≤ model.height event.ranked.target)
    (left right : RankedFinalityLock model events)
    (leftAccepted : accepted left) (rightAccepted : accepted right) :
    system.tree.reaches left.locked right.locked ∨
      system.tree.reaches right.locked left.locked :=
  rankedFinalityAgreementAux model honest events history accepted overlap q3Lock
    (model.height left.root + model.height right.root) left right (Nat.le_refl _)
    leftAccepted rightAccepted

end BFT
