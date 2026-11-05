import ReachableSafety

/-!
# Protocol actions and executions

One protocol action may produce several safety-relevant effects. Proposal
construction can durably emit more than one Vote before the action finishes.
This module groups checked effects without depending on an implementation,
network scheduler, or persistence engine.
-/

namespace BFT

inductive ProtocolActionKind
  | signVote
  | propose
  | publishVote
  | publishProposal
  | deliverVote
  | deliverProposal
  | idle
  deriving DecidableEq, Repr

def ProtocolActionKind.emissionLimit : ProtocolActionKind → Nat
  | .signVote => 1
  | .propose => 2
  | .publishVote => 0
  | .publishProposal => 0
  | .deliverVote => 0
  | .deliverProposal => 0
  | .idle => 0

/-- The finite safety effects of one atomic protocol action. -/
inductive ActionEffects {α : Type} {system : FrontierSystem α}
    (model : HeightModel system) (authority : Authority) (honest : List ValidatorId) :
    ProtocolState system model → ProtocolState system model → Type
  | none (state) : ActionEffects model authority honest state state
  | next {before middle after} :
      ProtocolStep model authority honest before middle →
      ActionEffects model authority honest middle after →
      ActionEffects model authority honest before after

def ProtocolStep.emittedVotes {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {authority : Authority}
    {honest : List ValidatorId} :
    {before after : ProtocolState system model} →
    ProtocolStep model authority honest before after → Nat
  | _, _, .stutter _ => 0
  | _, _, .admitCertificate .. => 0
  | _, _, .emitVote .. => 1
  | _, _, .applyAuthority .. => 0

def ActionEffects.emittedVotes {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {authority : Authority}
    {honest : List ValidatorId} :
    {before after : ProtocolState system model} →
    ActionEffects model authority honest before after → Nat
  | _, _, .none _ => 0
  | _, _, .next first rest => first.emittedVotes + rest.emittedVotes

/-- Each atomic action admits only the protocol effects that action can cause.
Publication and idle actions do not change receiver consensus state. -/
inductive ProtocolAction {α : Type} {system : FrontierSystem α}
    (model : HeightModel system) (authority : Authority) (honest : List ValidatorId) :
    ProtocolState system model → ProtocolState system model → Type
  | signVote {before after}
      (effects : ActionEffects model authority honest before after)
      (emissionBound : effects.emittedVotes ≤ 1) :
      ProtocolAction model authority honest before after
  | propose {before after}
      (effects : ActionEffects model authority honest before after)
      (emissionBound : effects.emittedVotes ≤ 2) :
      ProtocolAction model authority honest before after
  | publishVote (state) : ProtocolAction model authority honest state state
  | publishProposal (state) : ProtocolAction model authority honest state state
  | deliverVote {before after}
      (effects : ActionEffects model authority honest before after)
      (emissionBound : effects.emittedVotes ≤ 0) :
      ProtocolAction model authority honest before after
  | deliverProposal {before after}
      (effects : ActionEffects model authority honest before after)
      (emissionBound : effects.emittedVotes ≤ 0) :
      ProtocolAction model authority honest before after
  | idle (state) : ProtocolAction model authority honest state state

def ProtocolAction.kind {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {authority : Authority}
    {honest : List ValidatorId} {before after : ProtocolState system model}
    (action : ProtocolAction model authority honest before after) : ProtocolActionKind :=
  match action with
  | .signVote .. => .signVote
  | .propose .. => .propose
  | .publishVote .. => .publishVote
  | .publishProposal .. => .publishProposal
  | .deliverVote .. => .deliverVote
  | .deliverProposal .. => .deliverProposal
  | .idle .. => .idle

def ProtocolAction.effects {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {authority : Authority}
    {honest : List ValidatorId} :
    {before after : ProtocolState system model} →
    ProtocolAction model authority honest before after →
    ActionEffects model authority honest before after
  | _, _, .signVote effects _ => effects
  | _, _, .propose effects _ => effects
  | _, _, .publishVote state => .none state
  | _, _, .publishProposal state => .none state
  | _, _, .deliverVote effects _ => effects
  | _, _, .deliverProposal effects _ => effects
  | _, _, .idle state => .none state

theorem ProtocolAction.emissionBound {α : Type} {system : FrontierSystem α}
    {model : HeightModel system} {authority : Authority}
    {honest : List ValidatorId} {before after : ProtocolState system model}
    (action : ProtocolAction model authority honest before after) :
    action.effects.emittedVotes ≤ action.kind.emissionLimit := by
  cases action with
  | signVote effects bound => exact bound
  | propose effects bound => exact bound
  | publishVote => simp [ProtocolAction.effects, ProtocolAction.kind,
      ProtocolActionKind.emissionLimit, ActionEffects.emittedVotes]
  | publishProposal => simp [ProtocolAction.effects, ProtocolAction.kind,
      ProtocolActionKind.emissionLimit, ActionEffects.emittedVotes]
  | deliverVote effects bound => exact bound
  | deliverProposal effects bound => exact bound
  | idle => simp [ProtocolAction.effects, ProtocolAction.kind,
      ProtocolActionKind.emissionLimit, ActionEffects.emittedVotes]

/-- A complete protocol execution begins at Genesis. -/
inductive ProtocolExecution {α : Type} {system : FrontierSystem α}
    (model : HeightModel system) (authority : Authority) (honest : List ValidatorId) :
    ProtocolState system model → Prop
  | genesis : ProtocolExecution model authority honest (ProtocolState.genesis model)
  | action {before after} :
      ProtocolExecution model authority honest before →
      ProtocolAction model authority honest before after →
      ProtocolExecution model authority honest after

theorem ActionEffects.preserveReachable {α : Type}
    {system : FrontierSystem α} {model : HeightModel system}
    {authority : Authority} {honest : List ValidatorId}
    {before after : ProtocolState system model}
    (effects : ActionEffects model authority honest before after)
    (reachable : ReachableConsensus model authority honest before) :
    ReachableConsensus model authority honest after := by
  induction effects with
  | none => exact reachable
  | next first rest ih => exact ih (.step reachable first)

theorem ProtocolExecution.reachable {α : Type}
    {system : FrontierSystem α} {model : HeightModel system}
    {authority : Authority} {honest : List ValidatorId}
    {state : ProtocolState system model}
    (execution : ProtocolExecution model authority honest state) :
    ReachableConsensus model authority honest state := by
  induction execution with
  | genesis => exact .genesis
  | action earlier next ih => exact next.effects.preserveReachable ih

/-- Agreement for every protocol execution. -/
theorem ProtocolExecution.finalizedSafety {α : Type}
    {system : FrontierSystem α} {model : HeightModel system}
    {authority : Authority} {honest : List ValidatorId}
    {state : ProtocolState system model}
    (execution : ProtocolExecution model authority honest state)
    (unique : (authority.members.map Prod.fst).Nodup)
    (honestQuorum : authority.hasQuorum honest = true)
    (genesisBelow : ∀ block, system.tree.reaches model.genesis block)
    {left right : α} (leftFinalized : state.Finalized left)
    (rightFinalized : state.Finalized right) :
    system.tree.reaches left right ∨ system.tree.reaches right left := by
  exact execution.reachable.finalizedSafety unique honestQuorum genesisBelow
    leftFinalized rightFinalized

end BFT
