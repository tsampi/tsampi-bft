import Liveness
import ProtocolExecution

/-!
# Protocol-native conditional liveness

This module constructs protocol actions, accepted finality locks, and
`ProtocolState.Finalized` results from scheduled honest votes. The assumptions
do not contain protocol steps, actions, certificates, executions, or finality.
-/

namespace BFT

/-- Append one checked vote to the receiver state. -/
def ProtocolState.afterVote {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} (state : ProtocolState system model)
    (event : RankedVoteEvent system) : ProtocolState system model := {
  events := state.events ++ [event]
  locks := state.locks
  authorityTransitions := state.authorityTransitions
}

/-- Append one accepted finality lock to the receiver state. -/
def ProtocolState.afterLock {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} (state : ProtocolState system model)
    (lock : StoredFinalityLock model) : ProtocolState system model := {
  events := state.events
  locks := state.locks ++ [lock]
  authorityTransitions := state.authorityTransitions
}

/-- A finite suffix made only from checked protocol actions. -/
inductive ProtocolActionTrace {α : Type} {system : FrontierSystem α}
    (model : HeightModel system) (authority : Authority) (honest : List ValidatorId) :
    ProtocolState system model → ProtocolState system model → Prop
  | done (state) : ProtocolActionTrace model authority honest state state
  | next {before middle after} :
      ProtocolAction model authority honest before middle →
      ProtocolActionTrace model authority honest middle after →
      ProtocolActionTrace model authority honest before after

theorem ProtocolActionTrace.trans {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {authority : Authority} {honest : List ValidatorId}
    {first middle last : ProtocolState system model}
    (firstTrace : ProtocolActionTrace model authority honest first middle)
    (suffix : ProtocolActionTrace model authority honest middle last) :
    ProtocolActionTrace model authority honest first last := by
  induction firstTrace with
  | done => exact suffix
  | next action rest ih => exact .next action (ih suffix)

theorem ProtocolActionTrace.extend {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {authority : Authority} {honest : List ValidatorId}
    {before after : ProtocolState system model}
    (trace : ProtocolActionTrace model authority honest before after)
    (execution : ProtocolExecution model authority honest before) :
    ProtocolExecution model authority honest after := by
  induction trace with
  | done => exact execution
  | next action rest ih => exact ih (.action execution action)

/-- A raw sequence of delivered votes. Each constructor contains only the
checks performed when that vote is accepted, never a protocol transition. -/
inductive RawVoteSchedule {α : Type} {system : FrontierSystem α}
    (model : HeightModel system) (authority : Authority) (honest : List ValidatorId) :
    ProtocolState system model → ProtocolState system model → Type
  | done (state) : RawVoteSchedule model authority honest state state
  | vote {before after}
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
          model.height lock.root ≤ model.height event.ranked.target)
      (rest : RawVoteSchedule model authority honest
        (before.afterVote event) after) :
      RawVoteSchedule model authority honest before after

/-- The events carried by a raw delivery schedule, in delivery order. -/
def RawVoteSchedule.deliveredEvents {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {authority : Authority} {honest : List ValidatorId} :
    {before after : ProtocolState system model} →
    RawVoteSchedule model authority honest before after → List (RankedVoteEvent system)
  | _, _, .done _ => []
  | _, _, .vote event _ _ _ _ rest => event :: rest.deliveredEvents

theorem RawVoteSchedule.events_eq {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {authority : Authority} {honest : List ValidatorId}
    {before after : ProtocolState system model}
    (schedule : RawVoteSchedule model authority honest before after) :
    after.events = before.events ++ schedule.deliveredEvents := by
  induction schedule with
  | done => simp [RawVoteSchedule.deliveredEvents]
  | vote event freshTime freshBlock classified q3Ready rest ih =>
      simpa [RawVoteSchedule.deliveredEvents, ProtocolState.afterVote,
        List.append_assoc] using ih

theorem RawVoteSchedule.toTrace {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {authority : Authority} {honest : List ValidatorId}
    {before after : ProtocolState system model}
    (schedule : RawVoteSchedule model authority honest before after) :
    ProtocolActionTrace model authority honest before after := by
  induction schedule with
  | done state => exact .done state
  | vote event freshTime freshBlock classified q3Ready rest ih =>
      let step : ProtocolStep model authority honest _ _ :=
        .emitVote event freshTime freshBlock classified q3Ready
      let effects : ActionEffects model authority honest _ _ :=
        .next step (.none _)
      have bound : effects.emittedVotes ≤ 1 := by
        simp [effects, step, ActionEffects.emittedVotes, ProtocolStep.emittedVotes]
      exact .next (.signVote effects bound) ih

/-- Raw delivery of one valid vote from every honest validator for one target.
The contributors are derived from the schedule, and their quorum follows from
the stated reachable parent authority. -/
structure HonestVoteDelivery {α : Type} {system : FrontierSystem α}
    (model : HeightModel system) (authority : Authority) (honest : List ValidatorId)
    (before : ProtocolState system model) (locked : α) where
  root : α
  ready : ProtocolState system model
  schedule : RawVoteSchedule model authority honest before ready
  allHonestVotes : schedule.deliveredEvents.map RankedVoteEvent.signer = honest
  covers : ∀ event ∈ schedule.deliveredEvents,
    system.tree.reaches locked event.ranked.q2
  belowRoot : ∀ event ∈ schedule.deliveredEvents,
    model.height event.ranked.target < model.height root
  authorityEvidence : List CarriedEvidence
  evidenceSafe : ∀ item ∈ authorityEvidence, item.proof.offender ∉ honest
  honestQuorum : (authority.afterEvidence authorityEvidence).hasQuorum honest = true

def HonestVoteDelivery.lock {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {authority : Authority} {honest : List ValidatorId}
    {before : ProtocolState system model} {locked : α}
    (delivery : HonestVoteDelivery model authority honest before locked) :
    StoredFinalityLock model where
  locked := locked
  root := delivery.root
  contributors := delivery.schedule.deliveredEvents
  covers := delivery.covers
  belowRoot := delivery.belowRoot
  parentAuthority := authority.afterEvidence delivery.authorityEvidence
  authorityEvidence := delivery.authorityEvidence

theorem HonestVoteDelivery.valid {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {authority : Authority} {honest : List ValidatorId}
    {before : ProtocolState system model} {locked : α}
    (delivery : HonestVoteDelivery model authority honest before locked) :
    delivery.lock.ValidIn authority honest delivery.ready.events := by
  refine {
    stored := ?_
    parentFromRoot := rfl
    evidenceSafe := delivery.evidenceSafe
    quorum := ?_
  }
  · intro event member
    rw [delivery.schedule.events_eq]
    exact List.mem_append_right before.events member
  · change (authority.afterEvidence delivery.authorityEvidence).hasQuorum
      (delivery.schedule.deliveredEvents.map RankedVoteEvent.signer) = true
    rw [delivery.allHonestVotes]
    exact delivery.honestQuorum

def HonestVoteDelivery.after {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {authority : Authority} {honest : List ValidatorId}
    {before : ProtocolState system model} {locked : α}
    (delivery : HonestVoteDelivery model authority honest before locked) :
    ProtocolState system model :=
  delivery.ready.afterLock delivery.lock

theorem ProtocolStep.preserveFinalized {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {authority : Authority} {honest : List ValidatorId}
    {before after : ProtocolState system model} {block : α}
    (step : ProtocolStep model authority honest before after)
    (finalized : before.Finalized block) : after.Finalized block := by
  cases step with
  | stutter => exact finalized
  | admitCertificate lock _ =>
      rcases finalized with genesis | ⟨stored, member, locked⟩
      · exact Or.inl genesis
      · exact Or.inr ⟨stored, List.mem_append_left [lock] member, locked⟩
  | emitVote => exact finalized
  | applyAuthority => exact finalized

theorem ActionEffects.preserveFinalized {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {authority : Authority} {honest : List ValidatorId}
    {before after : ProtocolState system model} {block : α}
    (effects : ActionEffects model authority honest before after)
    (finalized : before.Finalized block) : after.Finalized block := by
  induction effects with
  | none => exact finalized
  | next first rest ih => exact ih (first.preserveFinalized finalized)

theorem ProtocolAction.preserveFinalized {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {authority : Authority} {honest : List ValidatorId}
    {before after : ProtocolState system model} {block : α}
    (action : ProtocolAction model authority honest before after)
    (finalized : before.Finalized block) : after.Finalized block :=
  action.effects.preserveFinalized finalized

theorem ProtocolActionTrace.preserveFinalized {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {authority : Authority} {honest : List ValidatorId}
    {before after : ProtocolState system model} {block : α}
    (trace : ProtocolActionTrace model authority honest before after)
    (finalized : before.Finalized block) : after.Finalized block := by
  induction trace with
  | done => exact finalized
  | next action rest ih => exact ih (action.preserveFinalized finalized)

theorem HonestVoteDelivery.toTrace {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {authority : Authority} {honest : List ValidatorId}
    {before : ProtocolState system model} {locked : α}
    (delivery : HonestVoteDelivery model authority honest before locked) :
    ProtocolActionTrace model authority honest before delivery.after := by
  let step : ProtocolStep model authority honest delivery.ready delivery.after :=
    .admitCertificate delivery.lock delivery.valid
  let effects : ActionEffects model authority honest delivery.ready delivery.after :=
    .next step (.none _)
  have bound : effects.emittedVotes ≤ 0 := by
    simp [effects, step, ActionEffects.emittedVotes, ProtocolStep.emittedVotes]
  exact delivery.schedule.toTrace.trans
    (.next (.deliverProposal effects bound) (.done delivery.after))

theorem HonestVoteDelivery.finalized {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {authority : Authority} {honest : List ValidatorId}
    {before : ProtocolState system model} {locked : α}
    (delivery : HonestVoteDelivery model authority honest before locked) :
    delivery.after.Finalized locked := by
  exact Or.inr ⟨delivery.lock, by simp [HonestVoteDelivery.after,
    ProtocolState.afterLock], rfl⟩

/-- Continued honest activity finalizes the selected target and then one valid
strict descendant. It contains only proposal data and delivered raw votes. -/
structure ContinuedHonestActivity {system : FrontierSystem Chain}
    (model : HeightModel system) (authority : Authority) (honest : List ValidatorId)
    (state : ProtocolState system model) (selected : Chain)
    (validCandidate : Chain → Prop) where
  selectedVotes : HonestVoteDelivery model authority honest state selected
  descendant : Chain
  descendantValid : validCandidate descendant
  descends : system.tree.reaches selected descendant
  progresses : descendant ≠ selected
  descendantVotes : HonestVoteDelivery model authority honest
    selectedVotes.after descendant

/-- Conditional liveness in the same execution and finality universe as
`ProtocolExecution.finalizedSafety`. Every action, transition, accepted lock,
execution suffix, and finality fact is derived from raw honest activity. -/
theorem ProtocolExecution.rankedConditionalLiveness
    {system : FrontierSystem Chain} {model : HeightModel system}
    {authority : Authority} {honest : List ValidatorId}
    {state : ProtocolState system model}
    (execution : ProtocolExecution model authority honest state)
    (validCandidate : Chain → Prop)
    (inventory : CanonicalInventory validCandidate)
    (observed : ValidatorId → List Chain)
    (delivery : EventualDelivery honest observed inventory.candidates)
    (activity : ContinuedHonestActivity model authority honest state
      inventory.selected validCandidate) :
    ∃ after descendant,
      ProtocolActionTrace model authority honest state after ∧
      ProtocolExecution model authority honest after ∧
      (∀ validator ∈ honest,
        selectedCandidate (observed validator) = some inventory.selected) ∧
      validCandidate inventory.selected ∧
      (∀ candidate ∈ inventory.candidates,
        compareChains inventory.selected candidate ≠ .gt) ∧
      validCandidate descendant ∧
      after.Consistent authority honest ∧
      after.Finalized inventory.selected ∧
      after.Finalized descendant ∧
      system.tree.reaches inventory.selected descendant ∧
      descendant ≠ inventory.selected := by
  let selectedTrace := activity.selectedVotes.toTrace
  let descendantTrace := activity.descendantVotes.toTrace
  let trace := selectedTrace.trans descendantTrace
  let after := activity.descendantVotes.after
  have finalExecution : ProtocolExecution model authority honest after :=
    trace.extend execution
  have selectedFinalized : after.Finalized inventory.selected :=
    descendantTrace.preserveFinalized activity.selectedVotes.finalized
  refine ⟨after, activity.descendant, trace, finalExecution, ?_,
    inventory.selectedValid, inventory.selectedBest, activity.descendantValid,
    finalExecution.reachable.consistent, selectedFinalized,
    activity.descendantVotes.finalized, activity.descends, activity.progresses⟩
  intro validator member
  rw [delivery.delivered validator member]
  exact inventory.selectedAtHead

private theorem dropLast_mono_prefix {left right : Chain}
    (reaches : List.IsPrefix left right) :
    List.IsPrefix left.dropLast right.dropLast := by
  rcases reaches with ⟨suffix, rfl⟩
  cases suffix with
  | nil => simp
  | cons block rest =>
      rw [List.dropLast_append_cons]
      exact (List.dropLast_prefix _).trans (List.prefix_append _ _)

/-- The witness uses newest-to-older frontier iteration: one frontier step
removes the newest block from the exact chain. -/
private def protocolWitnessSystem : FrontierSystem Chain where
  tree := prefixChainTree
  frontier := List.dropLast
  frontierBelow := List.dropLast_prefix
  frontierMonotone := dropLast_mono_prefix

private def protocolWitnessModel : HeightModel protocolWitnessSystem where
  height := List.length
  reachesHeight := List.IsPrefix.length_le
  sameHeight := fun reaches same ↦ reaches.eq_of_length same
  genesis := []
  genesisHeight := rfl
  zeroIsGenesis := fun _ zero ↦ List.eq_nil_of_length_eq_zero zero

private def protocolWitnessBlock (id position : Nat) : Block := {
  id := id
  proposerVote := { signer := 0, position := position, score := 1 }
}

private def protocolWitnessAuthority : Authority := { members := [(0, 1)] }
private def protocolWitnessHonest : List ValidatorId := [0]
private def protocolWitnessFirst := protocolWitnessBlock 1 1
private def protocolWitnessSecond := protocolWitnessBlock 2 2
private def protocolWitnessThird := protocolWitnessBlock 3 3
private def protocolWitnessFourth := protocolWitnessBlock 4 4
private def protocolWitnessFifth := protocolWitnessBlock 5 5

private def protocolWitnessSelected : Chain := [protocolWitnessFirst]
private def protocolWitnessDescendant : Chain :=
  [protocolWitnessFirst, protocolWitnessSecond]
private def protocolWitnessFirstVoteTarget : Chain :=
  [protocolWitnessFirst, protocolWitnessSecond, protocolWitnessThird]
private def protocolWitnessSecondVoteTarget : Chain :=
  [protocolWitnessFirst, protocolWitnessSecond, protocolWitnessThird,
    protocolWitnessFourth]
private def protocolWitnessSecondRoot : Chain :=
  [protocolWitnessFirst, protocolWitnessSecond, protocolWitnessThird,
    protocolWitnessFourth, protocolWitnessFifth]

private def protocolWitnessFirstEvent : RankedVoteEvent protocolWitnessSystem := {
  time := 1
  signer := 0
  ranked := { target := protocolWitnessFirstVoteTarget }
}

private def protocolWitnessSecondEvent : RankedVoteEvent protocolWitnessSystem := {
  time := 2
  signer := 0
  ranked := { target := protocolWitnessSecondVoteTarget }
}

private theorem protocolWitnessFirstQ2 :
    protocolWitnessFirstEvent.ranked.q2 = protocolWitnessSelected := by
  rfl

private theorem protocolWitnessFirstQ3 :
    protocolWitnessFirstEvent.ranked.q3 = protocolWitnessModel.genesis := by
  rfl

private theorem protocolWitnessSecondQ2 :
    protocolWitnessSecondEvent.ranked.q2 = protocolWitnessDescendant := by
  rfl

private theorem protocolWitnessSecondQ3 :
    protocolWitnessSecondEvent.ranked.q3 = protocolWitnessSelected := by
  rfl

private def protocolWitnessStart :
    ProtocolState protocolWitnessSystem protocolWitnessModel :=
  ProtocolState.genesis protocolWitnessModel

private def protocolWitnessFirstReady :
    ProtocolState protocolWitnessSystem protocolWitnessModel :=
  protocolWitnessStart.afterVote protocolWitnessFirstEvent

private def protocolWitnessFirstSchedule :
    RawVoteSchedule protocolWitnessModel protocolWitnessAuthority
      protocolWitnessHonest protocolWitnessStart protocolWitnessFirstReady := by
  apply RawVoteSchedule.vote protocolWitnessFirstEvent
  · intro previous member
    simp [protocolWitnessStart, ProtocolState.genesis] at member
  · intro previous member
    simp [protocolWitnessStart, ProtocolState.genesis] at member
  · intro _ previous member _
    simp [protocolWitnessStart, ProtocolState.genesis] at member
  · exact Or.inl protocolWitnessFirstQ3
  · exact .done _

private theorem protocolWitnessFirstEvents :
    protocolWitnessFirstSchedule.deliveredEvents =
      [protocolWitnessFirstEvent] := by
  rfl

private def protocolWitnessFirstDelivery :
    HonestVoteDelivery protocolWitnessModel protocolWitnessAuthority
      protocolWitnessHonest protocolWitnessStart protocolWitnessSelected := {
  root := protocolWitnessSecondVoteTarget
  ready := protocolWitnessFirstReady
  schedule := protocolWitnessFirstSchedule
  allHonestVotes := rfl
  covers := by
    intro event member
    rw [protocolWitnessFirstEvents] at member
    simp only [List.mem_singleton] at member
    subst event
    rw [protocolWitnessFirstQ2]
    exact List.prefix_refl _
  belowRoot := by
    intro event member
    rw [protocolWitnessFirstEvents] at member
    simp only [List.mem_singleton] at member
    subst event
    decide
  authorityEvidence := []
  evidenceSafe := by simp
  honestQuorum := by decide
}

private def protocolWitnessSecondReady :
    ProtocolState protocolWitnessSystem protocolWitnessModel :=
  protocolWitnessFirstDelivery.after.afterVote protocolWitnessSecondEvent

private def protocolWitnessSecondSchedule :
    RawVoteSchedule protocolWitnessModel protocolWitnessAuthority
      protocolWitnessHonest protocolWitnessFirstDelivery.after
      protocolWitnessSecondReady := by
  apply RawVoteSchedule.vote protocolWitnessSecondEvent
  · intro previous member
    simp [protocolWitnessFirstDelivery, protocolWitnessFirstReady,
      protocolWitnessStart, HonestVoteDelivery.after, HonestVoteDelivery.lock,
      ProtocolState.afterLock, ProtocolState.afterVote, ProtocolState.genesis] at member
    rcases member with rfl
    decide
  · intro previous member _
    simp [protocolWitnessFirstDelivery, protocolWitnessFirstReady,
      protocolWitnessStart, HonestVoteDelivery.after, HonestVoteDelivery.lock,
      ProtocolState.afterLock, ProtocolState.afterVote, ProtocolState.genesis] at member
    rcases member with rfl
    decide
  · intro _ previous member _
    simp [protocolWitnessFirstDelivery, protocolWitnessFirstReady,
      protocolWitnessStart, HonestVoteDelivery.after, HonestVoteDelivery.lock,
      ProtocolState.afterLock, ProtocolState.afterVote, ProtocolState.genesis] at member
    rcases member with rfl
    apply CertifiedRankTransition.descendant
    exact List.prefix_append _ [_]
  · exact Or.inr ⟨protocolWitnessFirstDelivery.lock, by
      simp [protocolWitnessFirstDelivery, HonestVoteDelivery.after,
        ProtocolState.afterLock], protocolWitnessSecondQ3, by decide⟩
  · exact .done _

private theorem protocolWitnessSecondEvents :
    protocolWitnessSecondSchedule.deliveredEvents =
      [protocolWitnessSecondEvent] := by
  rfl

private def protocolWitnessSecondDelivery :
    HonestVoteDelivery protocolWitnessModel protocolWitnessAuthority
      protocolWitnessHonest protocolWitnessFirstDelivery.after
      protocolWitnessDescendant := {
  root := protocolWitnessSecondRoot
  ready := protocolWitnessSecondReady
  schedule := protocolWitnessSecondSchedule
  allHonestVotes := rfl
  covers := by
    intro event member
    rw [protocolWitnessSecondEvents] at member
    simp only [List.mem_singleton] at member
    subst event
    rw [protocolWitnessSecondQ2]
    exact List.prefix_refl _
  belowRoot := by
    intro event member
    rw [protocolWitnessSecondEvents] at member
    simp only [List.mem_singleton] at member
    subst event
    decide
  authorityEvidence := []
  evidenceSafe := by simp
  honestQuorum := by decide
}

private def protocolWitnessValid (chain : Chain) : Prop := chain ≠ []

private def protocolWitnessInventory :
    CanonicalInventory protocolWitnessValid := {
  candidates := [protocolWitnessSelected]
  selected := protocolWitnessSelected
  selectedAtHead := rfl
  selectedValid := by simp [protocolWitnessValid, protocolWitnessSelected]
  selectedBest := by
    intro candidate member
    simp only [List.mem_singleton] at member
    subst candidate
    simp
}

private def protocolWitnessObserved (_ : ValidatorId) : List Chain :=
  protocolWitnessInventory.candidates

private theorem protocolWitnessDelivery :
    EventualDelivery protocolWitnessHonest protocolWitnessObserved
      protocolWitnessInventory.candidates := by
  constructor
  intro _ _
  rfl

private def protocolWitnessActivity :
    ContinuedHonestActivity protocolWitnessModel protocolWitnessAuthority
      protocolWitnessHonest protocolWitnessStart protocolWitnessInventory.selected
      protocolWitnessValid := {
  selectedVotes := protocolWitnessFirstDelivery
  descendant := protocolWitnessDescendant
  descendantValid := by
    simp [protocolWitnessValid, protocolWitnessDescendant]
  descends := List.prefix_append _ [_]
  progresses := by decide
  descendantVotes := protocolWitnessSecondDelivery
}

/-- The complete theorem runs from Genesis under a nonempty authority and
finalizes a non-Genesis target and a valid strict descendant. -/
theorem rankedConditionalLiveness_nonempty_witness :
    ∃ after descendant,
      protocolWitnessAuthority.members ≠ [] ∧
      protocolWitnessSelected ≠ protocolWitnessModel.genesis ∧
      descendant ≠ protocolWitnessModel.genesis ∧
      ProtocolActionTrace protocolWitnessModel protocolWitnessAuthority
        protocolWitnessHonest protocolWitnessStart after ∧
      ProtocolExecution protocolWitnessModel protocolWitnessAuthority
        protocolWitnessHonest after ∧
      after.Consistent protocolWitnessAuthority protocolWitnessHonest ∧
      after.Finalized protocolWitnessSelected ∧
      after.Finalized descendant ∧
      protocolWitnessValid protocolWitnessSelected ∧
      protocolWitnessValid descendant ∧
      protocolWitnessSystem.tree.reaches protocolWitnessSelected descendant ∧
      descendant ≠ protocolWitnessSelected := by
  have startExecution : ProtocolExecution protocolWitnessModel
      protocolWitnessAuthority protocolWitnessHonest protocolWitnessStart := .genesis
  obtain ⟨after, descendant, trace, execution, _, selectedValid, _,
      descendantValid, consistent, selectedFinalized, descendantFinalized,
      descends, progresses⟩ :=
    startExecution.rankedConditionalLiveness protocolWitnessValid
      protocolWitnessInventory protocolWitnessObserved protocolWitnessDelivery
      protocolWitnessActivity
  exact ⟨after, descendant, by decide, by decide, descendantValid, trace,
    execution, consistent, selectedFinalized, descendantFinalized, selectedValid,
    descendantValid, descends, progresses⟩

end BFT
