From Coq Require Import List Arith Bool Lia.
From BFT Require Import Protocol ConcreteProtocol Ranking Liveness ProtocolSafety.
Import ListNotations.

(** * Canonical concrete scan steps *)

Definition concrete_chain_tip (chain : Chain) : nat :=
  match rev chain with
  | [] => 0
  | block :: _ => block_id block
  end.

(** Safety and liveness share one concrete model: a target carries only its
    chain. Its layers are always the canonical projection from
    [ConcreteProtocol], never proof-carrying caller data. *)
Record ConcreteTarget (system : ConcreteProtocol) := mkConcreteTarget {
  concrete_chain : Chain
}.

Definition concrete_layers
    (system : ConcreteProtocol) (target : ConcreteTarget system) : list Layer :=
  protocol_layers system (concrete_chain system target).

Definition concrete_authority
    (system : ConcreteProtocol) (target : ConcreteTarget system) : Authority :=
  chain_authority system [] (concrete_chain system target).

Definition concrete_base
    (system : ConcreteProtocol) (chain : Chain) : ConcreteTarget system :=
  mkConcreteTarget system chain.

Definition concrete_child
    (system : ConcreteProtocol) (parent : ConcreteTarget system)
    (block : Block) : ConcreteTarget system :=
  mkConcreteTarget system (concrete_chain system parent ++ [block]).

Lemma concrete_layers_nonempty : forall system (target : ConcreteTarget system),
  concrete_layers system target <> [].
Proof.
  intros system [chain]. unfold concrete_layers, protocol_layers. simpl.
  intro impossible. apply app_eq_nil in impossible. intuition discriminate.
Qed.

(** * Protocol-native execution liveness *)

Definition safety_after_vote
    (state : SafetyState) (event : SignedTarget) : SafetyState :=
  mkSafetyState (safety_events state ++ [event])
    (safety_certificates state) (safety_authority_transitions state).

Definition safety_after_certificate
    (state : SafetyState) (certificate : ProtocolCertificate) : SafetyState :=
  mkSafetyState (safety_events state)
    (safety_certificates state ++ [certificate])
    (safety_authority_transitions state).

Definition safety_after_authority
    (state : SafetyState) (transition : CarrierAuthorityTransition) : SafetyState :=
  mkSafetyState (safety_events state) (safety_certificates state)
    (safety_authority_transitions state ++ [transition]).

(** A finite suffix of checked protocol actions, indexed by its exact start and
    finish states. *)
Inductive ProjectedActionTrace
    (system : ConcreteProtocol) (authority : Authority) (honest : list nat) :
    SafetyState -> SafetyState -> Type :=
| projected_trace_done : forall state,
    ProjectedActionTrace system authority honest state state
| projected_trace_next : forall before middle after,
    ProjectedAction system authority honest before middle ->
    ProjectedActionTrace system authority honest middle after ->
    ProjectedActionTrace system authority honest before after.

Lemma projected_action_trace_trans :
  forall system authority honest first middle last,
    ProjectedActionTrace system authority honest first middle ->
    ProjectedActionTrace system authority honest middle last ->
    ProjectedActionTrace system authority honest first last.
Proof.
  intros system authority honest first middle last prefix suffix.
  induction prefix as [state | before next middle action rest IH].
  - exact suffix.
  - exact (projected_trace_next system authority honest before next last
      action (IH suffix)).
Defined.

Lemma projected_action_trace_extend :
  forall system authority honest before after,
    ProjectedActionTrace system authority honest before after ->
    ProjectedExecution system authority honest before ->
    ProjectedExecution system authority honest after.
Proof.
  intros system authority honest before after trace execution.
  induction trace as [state | first middle last action rest IH].
  - exact execution.
  - apply IH. exact (projected_action system authority honest first middle
      execution action).
Qed.

Lemma safety_step_certificates_mono :
  forall system authority honest before after,
    SafetyStep system authority honest before after ->
    forall certificate,
      In certificate (safety_certificates before) ->
      In certificate (safety_certificates after).
Proof.
  intros system authority honest before after step certificate member.
  destruct step; simpl in *; try exact member.
  apply in_app_iff. left. exact member.
Qed.

Lemma safety_step_preserves_finalized :
  forall system authority honest before after chain,
    SafetyStep system authority honest before after ->
    SafetyFinalized before chain ->
    SafetyFinalized after chain.
Proof.
  intros system authority honest before after chain step finalized.
  destruct finalized as [genesis | [certificate [stored locked]]].
  - now left.
  - right. exists certificate. split.
    + eapply safety_step_certificates_mono; eauto.
    + exact locked.
Qed.

Lemma safety_effects_preserve_finalized :
  forall system authority honest before after chain,
    SafetyEffects system authority honest before after ->
    SafetyFinalized before chain ->
    SafetyFinalized after chain.
Proof.
  intros system authority honest before after chain effects finalized.
  induction effects as [state | first middle last step rest IH].
  - exact finalized.
  - apply IH. eapply safety_step_preserves_finalized; eauto.
Qed.

Lemma projected_action_preserves_finalized :
  forall system authority honest before after chain,
    ProjectedAction system authority honest before after ->
    SafetyFinalized before chain ->
    SafetyFinalized after chain.
Proof.
  intros system authority honest before after chain action finalized.
  eapply safety_effects_preserve_finalized.
  - exact (ProjectedActionEffects system authority honest before after action).
  - exact finalized.
Qed.

Lemma projected_action_trace_preserves_finalized :
  forall system authority honest before after chain,
    ProjectedActionTrace system authority honest before after ->
    SafetyFinalized before chain ->
    SafetyFinalized after chain.
Proof.
  intros system authority honest before after chain trace finalized.
  induction trace as [state | first middle last action rest IH].
  - exact finalized.
  - apply IH. eapply projected_action_preserves_finalized; eauto.
Qed.

(** Raw delivered votes. Constructors carry the checks used by vote admission,
    never a [SafetyStep], [ProjectedAction], execution, certificate, or finality
    result. *)
Inductive RawVoteSchedule
    (system : ConcreteProtocol) (authority : Authority) (honest : list nat) :
    SafetyState -> SafetyState -> Type :=
| raw_votes_done : forall state,
    RawVoteSchedule system authority honest state state
| raw_votes_next : forall before after event
    (computed : TargetComputed system event)
    (authority_backed : EventAuthorityBacked system authority before event)
    (admission : Q3Admission before event),
    (forall previous, In previous (safety_events before) ->
      signed_time previous < signed_time event) ->
    (In (signed_signer event) honest -> forall previous,
      In previous (safety_events before) ->
      signed_signer previous = signed_signer event ->
      LocalSigningTransition before event admission previous) ->
    RawVoteSchedule system authority honest
      (safety_after_vote before event) after ->
    RawVoteSchedule system authority honest before after.

Fixpoint raw_vote_schedule_events
    (system : ConcreteProtocol) (authority : Authority) (honest : list nat)
    {before after : SafetyState}
    (schedule : RawVoteSchedule system authority honest before after) :
    list SignedTarget :=
  match schedule with
  | raw_votes_done _ _ _ _ => []
  | raw_votes_next _ _ _ _ _ event _ _ _ _ _ rest =>
      event :: raw_vote_schedule_events system authority honest rest
  end.

Lemma raw_vote_schedule_events_eq :
  forall system authority honest before after
    (schedule : RawVoteSchedule system authority honest before after),
    safety_events after =
      safety_events before ++
        raw_vote_schedule_events system authority honest schedule.
Proof.
  intros system authority honest before after schedule.
  induction schedule as
      [state | before after event computed backed admission fresh classified
       rest IH].
  - now rewrite app_nil_r.
  - simpl in *. rewrite IH. unfold safety_after_vote. simpl.
    now rewrite <- app_assoc.
Qed.

Lemma raw_vote_schedule_trace :
  forall system authority honest before after,
    RawVoteSchedule system authority honest before after ->
    ProjectedActionTrace system authority honest before after.
Proof.
  intros system authority honest before after schedule.
  induction schedule as
      [state | before after event computed backed admission fresh classified
       rest IH].
  - apply projected_trace_done.
  - pose (step := safety_emit_vote system authority honest before event
      computed backed admission fresh classified).
    pose (effects := effects_next system authority honest before
      (safety_after_vote before event) (safety_after_vote before event)
      step (effects_done system authority honest
        (safety_after_vote before event))).
    assert (action : ProjectedAction system authority honest before
        (safety_after_vote before event)).
    { refine (projected_sign_vote system authority honest before
        (safety_after_vote before event) effects _ _).
      - unfold effects, step. simpl. auto.
      - unfold effects. simpl. lia. }
    exact (projected_trace_next system authority honest before
      (safety_after_vote before event) after action IH).
Defined.

(** Python's [block_frontier], [quorums], and [historical_q3] at the chain
    boundary, expressed through the canonical concrete protocol projection. *)
Definition protocol_q1 (system : ConcreteProtocol) (target : Chain) : Chain :=
  protocol_frontier system target.

Definition protocol_q2 (system : ConcreteProtocol) (target : Chain) : Chain :=
  protocol_q1 system (protocol_q1 system target).

Definition protocol_q3 (system : ConcreteProtocol) (target : Chain) : Chain :=
  protocol_q1 system (protocol_q2 system target).

(** One raw delivery contains the votes and certificate ingredients. The
    certificate, its admission action, and finality are derived below. *)
Record HonestVoteDelivery
    (system : ConcreteProtocol) (authority : Authority) (honest : list nat)
    (before : SafetyState) (finalized : Chain) : Type := mkHonestVoteDelivery {
  delivery_root : Chain;
  delivery_target : Chain;
  delivery_finalized_from_q3 :
    finalized = protocol_q3 system delivery_target;
  delivery_ready : SafetyState;
  delivery_schedule :
    RawVoteSchedule system authority honest before delivery_ready;
  delivery_all_honest_votes :
    map signed_signer
      (raw_vote_schedule_events system authority honest delivery_schedule) =
      honest;
  delivery_covers : forall event,
    In event (raw_vote_schedule_events system authority honest
      delivery_schedule) ->
    chain_reaches finalized (signed_q2 event);
  delivery_below_root : forall event,
    In event (raw_vote_schedule_events system authority honest
      delivery_schedule) ->
    length (signed_target event) < length delivery_root;
  delivery_offenders : list nat;
  delivery_evidence_safe : forall offender,
    In offender delivery_offenders -> ~ In offender honest;
  delivery_honest_quorum :
    has_quorum (after_evidence authority delivery_offenders) honest = true;
  delivery_authority_evidence :
    after_evidence authority delivery_offenders = authority \/
    exists event transition,
      In event (raw_vote_schedule_events system authority honest
        delivery_schedule) /\
      In transition (safety_authority_transitions delivery_ready) /\
      ConcreteCarrierInChain system authority (signed_target event) transition /\
      transition_child transition =
        after_evidence authority delivery_offenders
}.

Definition honest_delivery_certificate
    (system : ConcreteProtocol) (authority : Authority) (honest : list nat)
    (before : SafetyState) (finalized : Chain)
    (delivery : HonestVoteDelivery system authority honest before finalized) :
    ProtocolCertificate.
Proof.
  refine
    {| protocol_finalized := finalized;
       protocol_lock := finalized;
       protocol_covered := chain_reaches_refl finalized;
       protocol_root := delivery_root system authority honest before finalized
         delivery;
       protocol_contributors := raw_vote_schedule_events system authority honest
         (delivery_schedule system authority honest before finalized delivery);
       protocol_offenders := delivery_offenders system authority honest before
         finalized delivery |}.
  - exact (delivery_covers system authority honest before finalized delivery).
  - exact (delivery_below_root system authority honest before finalized delivery).
Defined.

Lemma honest_delivery_certificate_valid :
  forall system authority honest before finalized
    (delivery : HonestVoteDelivery system authority honest before finalized),
    CertificateValidIn authority honest
      (safety_events
        (delivery_ready system authority honest before finalized delivery))
      (honest_delivery_certificate system authority honest before finalized
        delivery).
Proof.
  intros system authority honest before finalized delivery.
  destruct delivery as
      [root target finalized_q3 ready schedule all_honest covers below offenders
       safe quorum backed].
  constructor; simpl in *.
  - intros event member. rewrite (raw_vote_schedule_events_eq system authority
      honest before ready schedule). apply in_app_iff. right. exact member.
  - exact safe.
  - unfold certificate_signers. simpl. rewrite all_honest. exact quorum.
Qed.

Lemma honest_delivery_certificate_authority_backed :
  forall system authority honest before finalized
    (delivery : HonestVoteDelivery system authority honest before finalized),
    CertificateAuthorityBacked system authority
      (delivery_ready system authority honest before finalized delivery)
      (honest_delivery_certificate system authority honest before finalized
        delivery).
Proof.
  intros system authority honest before finalized delivery.
  destruct delivery as
      [root target finalized_q3 ready schedule all_honest covers below offenders
       safe quorum backed].
  simpl in *. exact backed.
Qed.

Definition honest_delivery_after
    (system : ConcreteProtocol) (authority : Authority) (honest : list nat)
    (before : SafetyState) (finalized : Chain)
    (delivery : HonestVoteDelivery system authority honest before finalized) :
    SafetyState :=
  safety_after_certificate
    (delivery_ready system authority honest before finalized delivery)
    (honest_delivery_certificate system authority honest before finalized
      delivery).

Lemma honest_delivery_trace :
  forall system authority honest before finalized
    (delivery : HonestVoteDelivery system authority honest before finalized),
    ProjectedActionTrace system authority honest before
      (honest_delivery_after system authority honest before finalized delivery).
Proof.
  intros system authority honest before finalized delivery.
  pose proof (raw_vote_schedule_trace system authority honest before
    (delivery_ready system authority honest before finalized delivery)
    (delivery_schedule system authority honest before finalized delivery))
    as votes_trace.
  pose (certificate := honest_delivery_certificate system authority honest
    before finalized delivery).
  pose (ready := delivery_ready system authority honest before finalized delivery).
  pose (step := safety_admit_certificate system authority honest ready certificate
    (honest_delivery_certificate_valid system authority honest before finalized
      delivery)
    (honest_delivery_certificate_authority_backed system authority honest before
      finalized delivery)).
  pose (after := honest_delivery_after system authority honest before finalized
    delivery).
  pose (effects := effects_next system authority honest ready after after step
    (effects_done system authority honest after)).
  assert (action : ProjectedAction system authority honest ready after).
  { refine (projected_deliver_proposal system authority honest ready after
      effects _ _).
    - unfold effects, step. simpl. auto.
    - unfold effects, step. simpl. lia. }
  eapply projected_action_trace_trans.
  - exact votes_trace.
  - exact (projected_trace_next system authority honest ready after after action
      (projected_trace_done system authority honest after)).
Defined.

Lemma honest_delivery_finalized :
  forall system authority honest before finalized
    (delivery : HonestVoteDelivery system authority honest before finalized),
    SafetyFinalized
      (honest_delivery_after system authority honest before finalized delivery)
      finalized.
Proof.
  intros system authority honest before finalized delivery.
  right. exists (honest_delivery_certificate system authority honest before
    finalized delivery). split.
  - unfold honest_delivery_after, safety_after_certificate. simpl.
    apply in_app_iff. right. simpl. auto.
  - reflexivity.
Qed.

Lemma authority_transition_trace :
  forall system authority honest state transition,
    AuthorityTransitionValidFrom authority honest transition ->
    ProjectedActionTrace system authority honest state
      (safety_after_authority state transition).
Proof.
  intros system authority honest state transition valid.
  pose (step := safety_apply_authority system authority honest state transition
    valid).
  pose (after := safety_after_authority state transition).
  pose (effects := effects_next system authority honest state after after step
    (effects_done system authority honest after)).
  assert (action : ProjectedAction system authority honest state after).
  { refine (projected_deliver_proposal system authority honest state after
      effects _ _).
    - unfold effects, step. simpl. auto.
    - unfold effects, step. simpl. lia. }
  exact (projected_trace_next system authority honest state after after action
    (projected_trace_done system authority honest after)).
Defined.

(** Continued honest activity contains proposal data and raw delivered votes.
    It contains no certificate, protocol action, execution, or finality result. *)
Record ContinuedHonestActivity
    (system : ConcreteProtocol) (authority : Authority) (honest : list nat)
    (initial : SafetyState) (selected : Chain)
    (valid_candidate : Chain -> Prop) : Type := mkContinuedHonestActivity {
  selected_delivery :
    HonestVoteDelivery system authority honest initial selected;
  descendant_block : Block;
  descendant_transition : CarrierAuthorityTransition;
  descendant : Chain;
  descendant_exact_child :
    descendant = selected ++ [descendant_block];
  descendant_valid : valid_candidate descendant;
  descendant_carrier :
    ConcreteCarrierStep system authority selected descendant_block
      descendant_transition;
  descendant_authority_valid :
    AuthorityTransitionValidFrom authority honest descendant_transition;
  descendant_delivery : HonestVoteDelivery system authority honest
    (safety_after_authority
      (honest_delivery_after system authority honest initial selected
        selected_delivery)
      descendant_transition)
    descendant
}.

Record ProtocolLivenessResult
    (system : ConcreteProtocol) (authority : Authority) (honest : list nat)
    (initial : SafetyState) (valid_candidate : Chain -> Prop)
    (inventory : CanonicalInventory valid_candidate)
    (observed : nat -> list Chain) : Type := mkProtocolLivenessResult {
  result_descendant : Chain;
  result_final_state : SafetyState;
  result_trace : ProjectedActionTrace system authority honest initial
    result_final_state;
  result_execution : ProjectedExecution system authority honest
    result_final_state;
  result_observers_select : forall validator,
    In validator honest ->
    selected_candidate (observed validator) =
      Some (inventory_selected valid_candidate inventory);
  result_selected_valid :
    valid_candidate (inventory_selected valid_candidate inventory);
  result_selected_best : forall candidate,
    In candidate (inventory_candidates valid_candidate inventory) ->
    compare_chains (inventory_selected valid_candidate inventory) candidate <>
      Gt;
  result_descendant_valid : valid_candidate result_descendant;
  result_selected_q3 : exists target,
    inventory_selected valid_candidate inventory = protocol_q3 system target;
  result_descendant_q3 : exists target,
    result_descendant = protocol_q3 system target;
  result_exact_child : exists block,
    result_descendant =
      inventory_selected valid_candidate inventory ++ [block];
  result_valid_carrier : exists block transition,
    result_descendant =
      inventory_selected valid_candidate inventory ++ [block] /\
    ConcreteCarrierStep system authority
      (inventory_selected valid_candidate inventory) block transition /\
    AuthorityTransitionValidFrom authority honest transition;
  result_strict_progress :
    compare_chains result_descendant
      (inventory_selected valid_candidate inventory) = Lt;
  result_selected_finalized :
    SafetyFinalized result_final_state
      (inventory_selected valid_candidate inventory);
  result_descendant_finalized :
    SafetyFinalized result_final_state result_descendant;
  result_finalized_compatible :
    ChainCompatible (inventory_selected valid_candidate inventory)
      result_descendant
}.

(** Conditional liveness in the same execution and finality universe as
    [protocol_projected_execution_finalized_agreement]. *)
Theorem ranked_protocol_conditional_finality_liveness :
  forall system authority honest initial valid_candidate
      (inventory : CanonicalInventory valid_candidate) observed,
    has_quorum authority honest = true ->
    ProjectedExecution system authority honest initial ->
    EventualDelivery honest observed
      (inventory_candidates valid_candidate inventory) ->
    ContinuedHonestActivity system authority honest initial
      (inventory_selected valid_candidate inventory) valid_candidate ->
    ProtocolLivenessResult system authority honest initial valid_candidate
      inventory observed.
Proof.
  intros system authority honest initial valid_candidate inventory observed
    honest_quorum execution delivered activity.
  destruct activity as
      [selected_votes block transition child exact_child child_valid carrier
       transition_valid child_votes].
  pose proof (delivery_finalized_from_q3 system authority honest initial
    (inventory_selected valid_candidate inventory) selected_votes) as selected_q3.
  pose proof (delivery_finalized_from_q3 system authority honest
    (safety_after_authority
      (honest_delivery_after system authority honest initial
        (inventory_selected valid_candidate inventory) selected_votes)
      transition) child child_votes) as child_q3.
  pose proof (honest_delivery_trace system authority honest initial
    (inventory_selected valid_candidate inventory) selected_votes)
    as selected_trace.
  pose proof (authority_transition_trace system authority honest
    (honest_delivery_after system authority honest initial
      (inventory_selected valid_candidate inventory) selected_votes)
    transition transition_valid) as transition_trace.
  pose proof (honest_delivery_trace system authority honest
    (safety_after_authority
      (honest_delivery_after system authority honest initial
        (inventory_selected valid_candidate inventory) selected_votes)
      transition) child child_votes) as child_trace.
  pose proof (projected_action_trace_trans system authority honest initial
    (honest_delivery_after system authority honest initial
      (inventory_selected valid_candidate inventory) selected_votes)
    (safety_after_authority
      (honest_delivery_after system authority honest initial
        (inventory_selected valid_candidate inventory) selected_votes)
      transition) selected_trace transition_trace) as selected_and_transition.
  pose proof (projected_action_trace_trans system authority honest initial
    (safety_after_authority
      (honest_delivery_after system authority honest initial
        (inventory_selected valid_candidate inventory) selected_votes)
      transition)
    (honest_delivery_after system authority honest
      (safety_after_authority
        (honest_delivery_after system authority honest initial
          (inventory_selected valid_candidate inventory) selected_votes)
        transition) child child_votes)
    selected_and_transition child_trace) as whole_trace.
  pose proof (projected_action_trace_extend system authority honest initial
    (honest_delivery_after system authority honest
      (safety_after_authority
        (honest_delivery_after system authority honest initial
          (inventory_selected valid_candidate inventory) selected_votes)
        transition) child child_votes)
    whole_trace execution) as final_execution.
  pose proof (honest_delivery_finalized system authority honest initial
    (inventory_selected valid_candidate inventory) selected_votes)
    as selected_finalized_before_child.
  pose proof (projected_action_trace_preserves_finalized system authority honest
    (honest_delivery_after system authority honest initial
      (inventory_selected valid_candidate inventory) selected_votes)
    (safety_after_authority
      (honest_delivery_after system authority honest initial
        (inventory_selected valid_candidate inventory) selected_votes)
      transition)
    (inventory_selected valid_candidate inventory) transition_trace
    selected_finalized_before_child) as selected_after_transition.
  pose proof (projected_action_trace_preserves_finalized system authority honest
    (safety_after_authority
      (honest_delivery_after system authority honest initial
        (inventory_selected valid_candidate inventory) selected_votes)
      transition)
    (honest_delivery_after system authority honest
      (safety_after_authority
        (honest_delivery_after system authority honest initial
          (inventory_selected valid_candidate inventory) selected_votes)
        transition) child child_votes)
    (inventory_selected valid_candidate inventory) child_trace
    selected_after_transition) as selected_finalized.
  pose proof (honest_delivery_finalized system authority honest
    (safety_after_authority
      (honest_delivery_after system authority honest initial
        (inventory_selected valid_candidate inventory) selected_votes)
      transition) child child_votes) as child_finalized.
  assert (strict_progress : compare_chains child
      (inventory_selected valid_candidate inventory) = Lt).
  { rewrite exact_child. apply compare_chains_descendant. discriminate. }
  assert (compatible : ChainCompatible
      (inventory_selected valid_candidate inventory) child).
  { eapply protocol_projected_execution_finalized_agreement; eauto. }
  refine
    {| result_descendant := child;
       result_final_state := honest_delivery_after system authority honest
         (safety_after_authority
           (honest_delivery_after system authority honest initial
             (inventory_selected valid_candidate inventory) selected_votes)
           transition) child child_votes;
       result_trace := whole_trace;
       result_execution := final_execution;
       result_selected_valid := selected_valid valid_candidate inventory;
       result_selected_best := selected_best valid_candidate inventory;
       result_descendant_valid := child_valid;
       result_selected_q3 := ex_intro _
         (delivery_target system authority honest initial
           (inventory_selected valid_candidate inventory) selected_votes)
         selected_q3;
       result_descendant_q3 := ex_intro _
         (delivery_target system authority honest
           (safety_after_authority
             (honest_delivery_after system authority honest initial
               (inventory_selected valid_candidate inventory) selected_votes)
             transition) child child_votes)
         child_q3;
       result_exact_child := ex_intro _ block exact_child;
       result_valid_carrier := ex_intro _ block
         (ex_intro _ transition
           (conj exact_child (conj carrier transition_valid)));
       result_strict_progress := strict_progress;
       result_selected_finalized := selected_finalized;
       result_descendant_finalized := child_finalized;
       result_finalized_compatible := compatible |}.
  intros validator member.
  rewrite (eventually_delivered honest observed
    (inventory_candidates valid_candidate inventory) delivered validator member).
  exact (selected_at_head valid_candidate inventory).
Defined.

Lemma concrete_target_matches : forall system (target : ConcreteTarget system),
  scanned_target (concrete_layers system target) =
    concrete_chain_tip (concrete_chain system target).
Proof.
  intros system [chain]. unfold concrete_layers, protocol_layers,
    concrete_chain_tip, scanned_target. simpl.
  destruct (rev chain); reflexivity.
Qed.

Lemma concrete_layers_head_authority :
  forall system (target : ConcreteTarget system) layer rest,
    concrete_layers system target = layer :: rest ->
    layer_authority layer = concrete_authority system target.
Proof.
  intros system [chain] layer rest layers.
  unfold concrete_layers, protocol_layers, concrete_authority,
    chain_authority in *; simpl in *.
  destruct (rev chain) as [|block tail] eqn:reversed; simpl in layers.
  - inversion layers. reflexivity.
  - inversion layers. reflexivity.
Qed.

(** A child appends exactly one Block. Its authority is the parent authority
    after carried evidence, and its stored parent signers are the quorum used
    to scan back to that parent. *)
Inductive ConcreteQuorumStep
    (system : ConcreteProtocol)
    (honest : list nat) (endorsed : nat -> ConcreteTarget system -> Prop)
    (parent child : ConcreteTarget system) : Prop :=
| concrete_quorum_step : forall block transition,
    child = concrete_child system parent block ->
    ConcreteCarrierStep system (concrete_authority system parent)
      (concrete_chain system parent) block transition ->
    transition_signers transition = honest ->
    (forall signer, In signer honest -> endorsed signer parent) ->
    ConcreteQuorumStep system honest endorsed parent child.

Lemma chain_authority_at_current : forall system (target : ConcreteTarget system),
  chain_authority system (concrete_authority system target)
    (concrete_chain system target) = concrete_authority system target.
Proof.
  intros system [chain]. unfold concrete_authority, chain_authority. simpl.
  destruct (rev chain); reflexivity.
Qed.

Lemma concrete_quorum_step_parent_quorum :
  forall system honest endorsed parent child,
    ConcreteQuorumStep system honest endorsed parent child ->
    has_quorum (concrete_authority system parent) honest = true.
Proof.
  intros system honest endorsed parent child step.
  destruct step as [block transition built carrier signers validated].
  pose proof (transition_admitted_by_parent transition) as quorum.
  rewrite (carrier_transition_parent _ _ _ _ _ carrier),
    chain_authority_at_current, signers in quorum.
  exact quorum.
Qed.

Lemma concrete_quorum_step_carrier :
  forall system honest endorsed parent child,
    ConcreteQuorumStep system honest endorsed parent child ->
    exists block transition,
      child = concrete_child system parent block /\
      ConcreteCarrierStep system (concrete_authority system parent)
        (concrete_chain system parent) block transition.
Proof.
  intros system honest endorsed parent child step.
  destruct step as [block transition built carrier signers validated].
  exists block, transition. auto.
Qed.

Lemma concrete_quorum_step_child_authority :
  forall system honest endorsed parent child,
    ConcreteQuorumStep system honest endorsed parent child ->
    exists offenders,
      concrete_authority system child =
        after_evidence (concrete_authority system parent) offenders.
Proof.
  intros system honest endorsed parent child step.
  destruct step as [block transition built carrier signers validated].
  exists (transition_child_offenders transition). subst child.
  unfold concrete_child, concrete_authority, chain_authority. simpl.
  rewrite rev_app_distr. simpl.
  rewrite <- (carrier_transition_child _ _ _ _ _ carrier),
    transition_child_from_evidence,
    (carrier_transition_parent _ _ _ _ _ carrier),
    chain_authority_at_current.
  reflexivity.
Qed.

Lemma concrete_quorum_step_q1 :
  forall system honest endorsed parent child,
    ConcreteQuorumStep system honest endorsed parent child ->
    q1 (concrete_layers system child) = concrete_layers system parent.
Proof.
  intros system honest endorsed parent child step.
  pose proof (concrete_quorum_step_parent_quorum system honest endorsed
    parent child step) as quorum.
  destruct step as [block transition built carrier signers validated].
  assert (block_signers :
      protocol_block_parent_signers system block = honest).
  { rewrite <- (carrier_transition_signers _ _ _ _ _ carrier). exact signers. }
  subst child. unfold concrete_layers, concrete_child. simpl.
  rewrite protocol_layers_app. simpl.
  remember (protocol_layers system (concrete_chain system parent))
    as parent_layers eqn:layers.
  destruct parent_layers as [|parent_layer rest].
  - exfalso. apply (concrete_layers_nonempty system parent).
    unfold concrete_layers. exact (eq_sym layers).
  - unfold q1. simpl.
    assert (parent_authority :
        layer_authority parent_layer = concrete_authority system parent).
    { apply concrete_layers_head_authority with (rest := rest).
      unfold concrete_layers. exact (eq_sym layers). }
    simpl. rewrite block_signers, parent_authority, quorum. reflexivity.
Qed.

Lemma concrete_quorum_step_descendant :
  forall system honest endorsed parent child,
    ConcreteQuorumStep system honest endorsed parent child ->
    exists block,
      concrete_chain system child = concrete_chain system parent ++ [block].
Proof.
  intros system honest endorsed parent child step.
  destruct step as [block transition built carrier signers validated].
  exists block. subst child. reflexivity.
Qed.

Lemma concrete_quorum_step_ranking :
  forall system honest endorsed parent child,
    ConcreteQuorumStep system honest endorsed parent child ->
    compare_chains (concrete_chain system child)
      (concrete_chain system parent) = Lt.
Proof.
  intros system honest endorsed parent child step.
  destruct (concrete_quorum_step_descendant system honest endorsed
    parent child step) as [block child_chain].
  rewrite child_chain. apply compare_chains_descendant. discriminate.
Qed.

Lemma three_concrete_quorum_steps_q3 :
  forall system honest endorsed base first second third,
    ConcreteQuorumStep system honest endorsed base first ->
    ConcreteQuorumStep system honest endorsed first second ->
    ConcreteQuorumStep system honest endorsed second third ->
    q3 (concrete_layers system third) = concrete_layers system base.
Proof.
  intros system honest endorsed base first second third step1 step2 step3.
  unfold q3, q2.
  rewrite (concrete_quorum_step_q1 system honest endorsed second third step3).
  rewrite (concrete_quorum_step_q1 system honest endorsed first second step2).
  exact (concrete_quorum_step_q1 system honest endorsed base first step1).
Qed.

(** * Ready-domain activity *)

Record ConcreteParentReady
    (system : ConcreteProtocol)
    (honest : list nat) (endorsed : nat -> ConcreteTarget system -> Prop)
    (parent : ConcreteTarget system) : Prop := mkConcreteParentReady {
  ready_parent_quorum :
    has_quorum (concrete_authority system parent) honest = true;
  ready_parent_endorsements : forall signer,
    In signer honest -> endorsed signer parent
}.

(** Activity proposes one concrete Block and evidence set. The native quorum
    step remains a theorem consequence rather than an oracle result. *)
Record ConcreteProtocolActivity
    (system : ConcreteProtocol)
    (honest : list nat) (endorsed : nat -> ConcreteTarget system -> Prop)
    (ready : ConcreteTarget system -> Prop) (base : ConcreteTarget system) : Prop :=
  mkConcreteProtocolActivity {
    activity_base_ready : ready base;
    activity_parent_ready : forall parent,
      ready parent -> ConcreteParentReady system honest endorsed parent;
    next_concrete_child : forall parent,
      ready parent -> exists block offenders,
        protocol_block_authority system block =
          after_evidence (concrete_authority system parent) offenders /\
        protocol_block_parent_signers system block = honest /\
        ready (concrete_child system parent block)
  }.

Lemma activity_concrete_quorum_step :
  forall system honest endorsed ready base,
    ConcreteProtocolActivity system honest endorsed ready base ->
    forall parent, ready parent ->
    exists child,
      ConcreteQuorumStep system honest endorsed parent child /\ ready child.
Proof.
  intros system honest endorsed ready base activity parent parent_ready.
  destruct (next_concrete_child system honest endorsed ready base activity
    parent parent_ready) as [block [offenders [authority [signers child_ready]]]].
  pose proof (activity_parent_ready system honest endorsed ready base activity
    parent parent_ready) as protocol_ready.
  destruct protocol_ready as [parent_quorum parent_endorsements].
  pose (transition := mkCarrierAuthorityTransition
    (concrete_authority system parent)
    (protocol_block_authority system block) honest [] offenders
    authority parent_quorum).
  exists (concrete_child system parent block). split.
  - apply concrete_quorum_step with (block := block) (transition := transition).
    + reflexivity.
    + constructor.
      * unfold transition. simpl. symmetry. apply chain_authority_at_current.
      * reflexivity.
      * unfold transition. simpl. symmetry. exact signers.
    + reflexivity.
    + exact parent_endorsements.
  - exact child_ready.
Qed.

Lemma after_evidence_nil : forall authority,
  after_evidence authority [] = authority.
Proof.
  intro authority. induction authority as [|[identity weight] rest IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Definition activity_extension_block : Block := mkBlock 0 0 0 0.

Definition concrete_ready_at
    (system : ConcreteProtocol) (authority : Authority)
    (target : ConcreteTarget system) : Prop :=
  concrete_chain system target <> [] /\
  concrete_authority system target = authority.

Lemma concrete_authority_constant_nonempty :
  forall system authority chain,
    (forall block, protocol_block_authority system block = authority) ->
    chain <> [] ->
    concrete_authority system (concrete_base system chain) = authority.
Proof.
  intros system authority chain constant nonempty.
  unfold concrete_authority, concrete_base, chain_authority. simpl.
  destruct (rev chain) as [|block rest] eqn:reversed.
  - apply (f_equal (@rev Block)) in reversed.
    rewrite rev_involutive in reversed. simpl in reversed. contradiction.
  - apply constant.
Qed.

(** The activity contract is inhabited for a canonical, nonempty base whenever
    the protocol assigns its Blocks the advertised authority and signers. *)
Lemma concrete_protocol_activity_inhabited :
  forall system chain authority honest,
    chain <> [] ->
    (forall block, protocol_block_authority system block = authority) ->
    (forall block, protocol_block_parent_signers system block = honest) ->
    has_quorum authority honest = true ->
    ConcreteProtocolActivity system honest (fun _ _ => True)
      (concrete_ready_at system authority) (concrete_base system chain).
Proof.
  intros system chain authority honest chain_nonempty constant_authority
    constant_signers honest_quorum. constructor.
  - split; [exact chain_nonempty |].
    now apply concrete_authority_constant_nonempty.
  - intros parent [_ parent_authority]. constructor.
    + rewrite parent_authority. exact honest_quorum.
    + intros. exact I.
  - intros parent [parent_nonempty parent_authority].
    exists activity_extension_block, [].
    rewrite constant_authority, parent_authority, after_evidence_nil.
    split; [reflexivity |].
    rewrite constant_signers. split; [reflexivity |].
    split.
    + unfold concrete_child. simpl. intro empty_child.
      apply app_eq_nil in empty_child. destruct empty_child as [_ impossible].
      discriminate.
    + unfold concrete_child, concrete_authority, chain_authority. simpl.
      rewrite rev_app_distr. simpl. apply constant_authority.
Qed.

(** * Ranked four-step liveness *)

Theorem ranked_concrete_protocol_conditional_liveness :
  forall system honest endorsed valid_candidate
      (inventory : CanonicalInventory valid_candidate) observed
      (ready : ConcreteTarget system -> Prop),
    EventualDelivery honest observed
      (inventory_candidates valid_candidate inventory) ->
    ConcreteProtocolActivity system honest endorsed ready
      (concrete_base system (inventory_selected valid_candidate inventory)) ->
    exists first second third fourth,
      (forall validator,
        In validator honest ->
        selected_candidate (observed validator) =
          Some (inventory_selected valid_candidate inventory)) /\
      valid_candidate (inventory_selected valid_candidate inventory) /\
      (forall ranked_candidate,
        In ranked_candidate (inventory_candidates valid_candidate inventory) ->
        compare_chains (inventory_selected valid_candidate inventory)
          ranked_candidate <> Gt) /\
      has_quorum (concrete_authority system
        (concrete_base system (inventory_selected valid_candidate inventory)))
        honest = true /\
      ConcreteQuorumStep system honest endorsed
        (concrete_base system (inventory_selected valid_candidate inventory)) first /\
      ConcreteQuorumStep system honest endorsed first second /\
      ConcreteQuorumStep system honest endorsed second third /\
      ConcreteQuorumStep system honest endorsed third fourth /\
      compare_chains (concrete_chain system first)
        (inventory_selected valid_candidate inventory) = Lt /\
      q3 (concrete_layers system third) =
        concrete_layers system (concrete_base system
          (inventory_selected valid_candidate inventory)) /\
      scanned_target (q3 (concrete_layers system third)) =
        concrete_chain_tip (inventory_selected valid_candidate inventory) /\
      q3 (concrete_layers system fourth) = concrete_layers system first /\
      exists block,
        concrete_chain system first =
          inventory_selected valid_candidate inventory ++ [block].
Proof.
  intros system honest endorsed valid_candidate inventory observed ready
    delivery activity.
  set (base := concrete_base system
    (inventory_selected valid_candidate inventory)) in *.
  pose proof (activity_base_ready system honest endorsed ready base activity)
    as base_ready.
  destruct (activity_concrete_quorum_step system honest endorsed ready base
    activity base base_ready) as [first [step1 first_ready]].
  destruct (activity_concrete_quorum_step system honest endorsed ready base
    activity first first_ready) as [second [step2 second_ready]].
  destruct (activity_concrete_quorum_step system honest endorsed ready base
    activity second second_ready) as [third [step3 third_ready]].
  destruct (activity_concrete_quorum_step system honest endorsed ready base
    activity third third_ready) as [fourth [step4 fourth_ready]].
  exists first, second, third, fourth.
  refine (conj _ (conj (selected_valid valid_candidate inventory) _)).
  - intros validator member.
    rewrite (eventually_delivered honest observed
      (inventory_candidates valid_candidate inventory)
      delivery validator member).
    exact (selected_at_head valid_candidate inventory).
  - refine (conj (selected_best valid_candidate inventory) _).
    refine (conj (concrete_quorum_step_parent_quorum system honest endorsed
      base first step1) _).
    refine (conj step1 (conj step2 (conj step3 (conj step4 _)))).
    refine (conj (concrete_quorum_step_ranking system honest endorsed
      base first step1) _).
    assert (third_q3 :
        q3 (concrete_layers system third) = concrete_layers system base).
    { exact (three_concrete_quorum_steps_q3 system honest endorsed
        base first second third step1 step2 step3). }
    assert (fourth_q3 :
        q3 (concrete_layers system fourth) = concrete_layers system first).
    { exact (three_concrete_quorum_steps_q3 system honest endorsed
        first second third fourth step2 step3 step4). }
    destruct (concrete_quorum_step_descendant system honest endorsed
      base first step1) as [block first_chain].
    refine (conj third_q3 (conj _ (conj fourth_q3 _))).
    + rewrite third_q3. subst base. apply concrete_target_matches.
    + exists block. subst base. exact first_chain.
Qed.


