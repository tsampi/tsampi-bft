From Coq Require Import List Lia.
From BFT Require Import Protocol ConcreteProtocol Ranking Liveness
  ProtocolSafety ProtocolLiveness.
Import ListNotations.

(** * Non-root safety execution *)

Definition bootstrap_authority : Authority := [(1, 5); (2, 1); (3, 1)].
Definition bootstrap_reduced_authority : Authority := [(1, 5); (2, 1)].
Definition bootstrap_honest : list nat := [1].

Definition bootstrap_block_one : Block := mkBlock 1 1 1 1.
Definition bootstrap_block_two : Block := mkBlock 2 1 2 2.
Definition bootstrap_block_three : Block := mkBlock 3 1 3 3.
Definition bootstrap_block_four : Block := mkBlock 4 1 4 4.

Definition bootstrap_system : ConcreteProtocol :=
  {| protocol_block_authority := fun block =>
       if Nat.eqb (block_id block) 1
       then bootstrap_authority
       else bootstrap_reduced_authority;
     protocol_block_parent_signers := fun _ => bootstrap_honest |}.

Definition bootstrap_root_transition : CarrierAuthorityTransition :=
  {| transition_parent := bootstrap_authority;
     transition_child := bootstrap_authority;
     transition_signers := bootstrap_honest;
     transition_parent_offenders := [];
     transition_child_offenders := [];
     transition_child_from_evidence := eq_refl;
     transition_admitted_by_parent := eq_refl |}.

Definition bootstrap_reduce_transition : CarrierAuthorityTransition :=
  {| transition_parent := bootstrap_authority;
     transition_child := bootstrap_reduced_authority;
     transition_signers := bootstrap_honest;
     transition_parent_offenders := [];
     transition_child_offenders := [3];
     transition_child_from_evidence := eq_refl;
     transition_admitted_by_parent := eq_refl |}.

Definition bootstrap_reduced_transition : CarrierAuthorityTransition :=
  {| transition_parent := bootstrap_reduced_authority;
     transition_child := bootstrap_reduced_authority;
     transition_signers := bootstrap_honest;
     transition_parent_offenders := [3];
     transition_child_offenders := [];
     transition_child_from_evidence := eq_refl;
     transition_admitted_by_parent := eq_refl |}.

Lemma bootstrap_root_transition_valid :
  AuthorityTransitionValidFrom bootstrap_authority bootstrap_honest
    bootstrap_root_transition.
Proof. constructor; simpl; intuition congruence. Qed.

Lemma bootstrap_reduce_transition_valid :
  AuthorityTransitionValidFrom bootstrap_authority bootstrap_honest
    bootstrap_reduce_transition.
Proof. constructor; simpl; intuition congruence. Qed.

Lemma bootstrap_reduced_transition_valid :
  AuthorityTransitionValidFrom bootstrap_authority bootstrap_honest
    bootstrap_reduced_transition.
Proof. constructor; simpl; intuition congruence. Qed.

Definition bootstrap_root_state : SafetyState :=
  mkSafetyState [] [] [bootstrap_root_transition].

Definition bootstrap_reduce_state : SafetyState :=
  mkSafetyState [] []
    [bootstrap_root_transition; bootstrap_reduce_transition].

Definition bootstrap_authority_state : SafetyState :=
  mkSafetyState [] []
    [bootstrap_root_transition; bootstrap_reduce_transition;
     bootstrap_reduced_transition].

Lemma bootstrap_apply_root :
  SafetyStep bootstrap_system bootstrap_authority bootstrap_honest
    genesis_safety_state bootstrap_root_state.
Proof.
  change (SafetyStep bootstrap_system bootstrap_authority bootstrap_honest
    genesis_safety_state
    (mkSafetyState [] [] ([] ++ [bootstrap_root_transition]))).
  apply safety_apply_authority. exact bootstrap_root_transition_valid.
Defined.

Lemma bootstrap_apply_reduce :
  SafetyStep bootstrap_system bootstrap_authority bootstrap_honest
    bootstrap_root_state bootstrap_reduce_state.
Proof.
  change (SafetyStep bootstrap_system bootstrap_authority bootstrap_honest
    bootstrap_root_state
    (mkSafetyState [] []
      ([bootstrap_root_transition] ++ [bootstrap_reduce_transition]))).
  apply safety_apply_authority. exact bootstrap_reduce_transition_valid.
Defined.

Lemma bootstrap_apply_reduced :
  SafetyStep bootstrap_system bootstrap_authority bootstrap_honest
    bootstrap_reduce_state bootstrap_authority_state.
Proof.
  change (SafetyStep bootstrap_system bootstrap_authority bootstrap_honest
    bootstrap_reduce_state
    (mkSafetyState [] []
      ([bootstrap_root_transition; bootstrap_reduce_transition] ++
        [bootstrap_reduced_transition]))).
  apply safety_apply_authority. exact bootstrap_reduced_transition_valid.
Defined.

Lemma bootstrap_first_carrier :
  ConcreteCarrierStep bootstrap_system bootstrap_authority []
    bootstrap_block_one bootstrap_root_transition.
Proof. constructor; reflexivity. Qed.

Lemma bootstrap_second_carrier :
  ConcreteCarrierStep bootstrap_system bootstrap_authority
    [bootstrap_block_one] bootstrap_block_two bootstrap_reduce_transition.
Proof. constructor; reflexivity. Qed.

Lemma bootstrap_third_carrier :
  ConcreteCarrierStep bootstrap_system bootstrap_authority
    [bootstrap_block_one; bootstrap_block_two]
    bootstrap_block_three bootstrap_reduced_transition.
Proof. constructor; reflexivity. Qed.

(** The transition has the right child authority, but the wrong parent for the
    third edge. A child-only transition lookup would make this false theorem
    provable, so it serves as the local mutation contract. *)
Lemma matching_child_transition_is_not_chain_local :
  ~ ConcreteCarrierStep bootstrap_system bootstrap_authority
      [bootstrap_block_one; bootstrap_block_two]
      bootstrap_block_three bootstrap_reduce_transition.
Proof.
  intro carrier.
  pose proof (carrier_transition_parent _ _ _ _ _ carrier) as parent.
  simpl in parent. discriminate.
Qed.

Definition bootstrap_target : Chain :=
  [bootstrap_block_one; bootstrap_block_two; bootstrap_block_three].

Definition bootstrap_event : SignedTarget :=
  mkSignedTarget 0 1 bootstrap_target
    [bootstrap_block_one; bootstrap_block_two] [bootstrap_block_one] [].

Definition bootstrap_arbitrary_lookup_state : SafetyState :=
  mkSafetyState [] []
    [bootstrap_root_transition; bootstrap_reduce_transition].

(** Even though [bootstrap_reduce_transition] has the same child authority as
    the third Block, omitting the non-root parent transition makes the event
    trace invalid. *)
Lemma arbitrary_stored_transition_lookup_rejected :
  ~ EventAuthorityBacked bootstrap_system bootstrap_authority
      bootstrap_arbitrary_lookup_state bootstrap_event.
Proof.
  intro backed.
  destruct (concrete_carrier_trace_last bootstrap_system bootstrap_authority
    [bootstrap_root_transition; bootstrap_reduce_transition]
    [bootstrap_block_one; bootstrap_block_two] bootstrap_block_three backed)
    as [transition [stored carrier]].
  simpl in stored. destruct stored as [root | [reduced | impossible]].
  - subst transition.
    pose proof (carrier_transition_child _ _ _ _ _ carrier) as child.
    simpl in child. discriminate.
  - subst transition. exact (matching_child_transition_is_not_chain_local carrier).
  - contradiction.
Qed.

Lemma bootstrap_event_computed : TargetComputed bootstrap_system bootstrap_event.
Proof. constructor; reflexivity. Qed.

Lemma bootstrap_event_carriers :
  EventAuthorityBacked bootstrap_system bootstrap_authority
    bootstrap_authority_state bootstrap_event.
Proof.
  unfold EventAuthorityBacked, bootstrap_event, bootstrap_target.
  simpl.
  apply carrier_trace_append with
    (prefix := [bootstrap_block_one; bootstrap_block_two])
    (block := bootstrap_block_three)
    (transition := bootstrap_reduced_transition).
  - apply carrier_trace_append with
      (prefix := [bootstrap_block_one])
      (block := bootstrap_block_two)
      (transition := bootstrap_reduce_transition).
    + apply carrier_trace_append with
        (prefix := [])
        (block := bootstrap_block_one)
        (transition := bootstrap_root_transition).
      * apply carrier_trace_genesis.
      * simpl. auto.
      * exact bootstrap_first_carrier.
    + simpl. auto.
    + exact bootstrap_second_carrier.
  - simpl. auto.
  - exact bootstrap_third_carrier.
Qed.

Definition bootstrap_vote_state : SafetyState :=
  mkSafetyState [bootstrap_event] []
    [bootstrap_root_transition; bootstrap_reduce_transition;
     bootstrap_reduced_transition].

Lemma bootstrap_emit_step :
  SafetyStep bootstrap_system bootstrap_authority bootstrap_honest
    bootstrap_authority_state bootstrap_vote_state.
Proof.
  apply safety_emit_vote with
    (admission := q3_at_genesis bootstrap_authority_state bootstrap_event eq_refl).
  - exact bootstrap_event_computed.
  - exact bootstrap_event_carriers.
  - simpl. intros. contradiction.
  - simpl. intros. contradiction.
Defined.

Definition bootstrap_certificate : ProtocolCertificate.
Proof.
  refine
    {| protocol_finalized := [bootstrap_block_one];
       protocol_lock := [bootstrap_block_one];
       protocol_covered := chain_reaches_refl [bootstrap_block_one];
       protocol_root :=
         [bootstrap_block_one; bootstrap_block_two;
          bootstrap_block_three; bootstrap_block_four];
       protocol_contributors := [bootstrap_event];
       protocol_offenders := [3] |}.
  - intros event member. simpl in member.
    destruct member as [same | impossible]; [subst event | contradiction].
    apply chain_reaches_refl.
  - intros event member. simpl in member.
    destruct member as [same | impossible]; [subst event | contradiction].
    simpl. lia.
Defined.

Lemma bootstrap_certificate_valid :
  CertificateValidIn bootstrap_authority bootstrap_honest
    (safety_events bootstrap_vote_state) bootstrap_certificate.
Proof.
  constructor.
  - simpl. intros event member. exact member.
  - simpl. intuition congruence.
  - reflexivity.
Qed.

Lemma bootstrap_certificate_authority_backed :
  CertificateAuthorityBacked bootstrap_system bootstrap_authority
    bootstrap_vote_state bootstrap_certificate.
Proof.
  right. exists bootstrap_event, bootstrap_reduced_transition.
  split; [simpl; auto |].
  split; [simpl; auto |].
  split.
  - exists [bootstrap_block_one; bootstrap_block_two],
      bootstrap_block_three, []. split.
    + reflexivity.
    + exact bootstrap_third_carrier.
  - reflexivity.
Qed.

Definition bootstrap_final_state : SafetyState :=
  mkSafetyState [bootstrap_event] [bootstrap_certificate]
    [bootstrap_root_transition; bootstrap_reduce_transition;
     bootstrap_reduced_transition].

Lemma bootstrap_admit_step :
  SafetyStep bootstrap_system bootstrap_authority bootstrap_honest
    bootstrap_vote_state bootstrap_final_state.
Proof.
  change (SafetyStep bootstrap_system bootstrap_authority bootstrap_honest
    bootstrap_vote_state
    (mkSafetyState (safety_events bootstrap_vote_state)
      (safety_certificates bootstrap_vote_state ++ [bootstrap_certificate])
      (safety_authority_transitions bootstrap_vote_state))).
  apply safety_admit_certificate.
  - exact bootstrap_certificate_valid.
  - exact bootstrap_certificate_authority_backed.
Defined.

Definition bootstrap_authority_effects : SafetyEffects bootstrap_system
    bootstrap_authority bootstrap_honest genesis_safety_state
    bootstrap_authority_state :=
  effects_next bootstrap_system bootstrap_authority bootstrap_honest
    genesis_safety_state bootstrap_root_state bootstrap_authority_state
    bootstrap_apply_root
    (effects_next bootstrap_system bootstrap_authority bootstrap_honest
      bootstrap_root_state bootstrap_reduce_state bootstrap_authority_state
      bootstrap_apply_reduce
      (effects_next bootstrap_system bootstrap_authority bootstrap_honest
        bootstrap_reduce_state bootstrap_authority_state
        bootstrap_authority_state bootstrap_apply_reduced
        (effects_done bootstrap_system bootstrap_authority bootstrap_honest
          bootstrap_authority_state))).

Lemma bootstrap_authority_action : ProjectedAction bootstrap_system
    bootstrap_authority bootstrap_honest genesis_safety_state
    bootstrap_authority_state.
Proof.
  refine (projected_deliver_vote bootstrap_system bootstrap_authority
    bootstrap_honest genesis_safety_state bootstrap_authority_state
    bootstrap_authority_effects _ _).
  - simpl. repeat split; trivial.
  - simpl. lia.
Qed.

Definition bootstrap_sign_effects : SafetyEffects bootstrap_system
    bootstrap_authority bootstrap_honest bootstrap_authority_state
    bootstrap_vote_state :=
  effects_next bootstrap_system bootstrap_authority bootstrap_honest
    bootstrap_authority_state bootstrap_vote_state bootstrap_vote_state
    bootstrap_emit_step
    (effects_done bootstrap_system bootstrap_authority bootstrap_honest
      bootstrap_vote_state).

Lemma bootstrap_sign_action : ProjectedAction bootstrap_system
    bootstrap_authority bootstrap_honest bootstrap_authority_state
    bootstrap_vote_state.
Proof.
  refine (projected_sign_vote bootstrap_system bootstrap_authority
    bootstrap_honest bootstrap_authority_state bootstrap_vote_state
    bootstrap_sign_effects _ _).
  - simpl. split; trivial.
  - simpl. lia.
Qed.

Definition bootstrap_delivery_effects : SafetyEffects bootstrap_system
    bootstrap_authority bootstrap_honest bootstrap_vote_state
    bootstrap_final_state :=
  effects_next bootstrap_system bootstrap_authority bootstrap_honest
    bootstrap_vote_state bootstrap_final_state bootstrap_final_state
    bootstrap_admit_step
    (effects_done bootstrap_system bootstrap_authority bootstrap_honest
      bootstrap_final_state).

Lemma bootstrap_delivery_action : ProjectedAction bootstrap_system
    bootstrap_authority bootstrap_honest bootstrap_vote_state
    bootstrap_final_state.
Proof.
  refine (projected_deliver_vote bootstrap_system bootstrap_authority
    bootstrap_honest bootstrap_vote_state bootstrap_final_state
    bootstrap_delivery_effects _ _).
  - simpl. split; trivial.
  - simpl. lia.
Qed.

Lemma bootstrap_projected_execution :
  ProjectedExecution bootstrap_system bootstrap_authority bootstrap_honest
    bootstrap_final_state.
Proof.
  apply projected_action with (before := bootstrap_vote_state).
  - apply projected_action with (before := bootstrap_authority_state).
    + apply projected_action with (before := genesis_safety_state).
      * apply projected_genesis.
      * exact bootstrap_authority_action.
    + exact bootstrap_sign_action.
  - exact bootstrap_delivery_action.
Qed.

Theorem protocol_projected_execution_nonempty_finality_inhabited :
  exists (system : ConcreteProtocol) (authority : Authority)
      (honest : list nat) (state : SafetyState) (finalized : Chain),
    finalized <> [] /\
    ProjectedExecution system authority honest state /\
    SafetyFinalized state finalized.
Proof.
  exists bootstrap_system, bootstrap_authority, bootstrap_honest,
    bootstrap_final_state, [bootstrap_block_one].
  split; [discriminate |]. split.
  - exact bootstrap_projected_execution.
  - right. exists bootstrap_certificate. simpl. auto.
Qed.

(** The agreement theorem is exercised on the same execution whose third
    Block is backed by a genuinely non-root parent transition. *)
Corollary bootstrap_nonempty_finality_agrees : forall other,
  SafetyFinalized bootstrap_final_state other ->
  ChainCompatible [bootstrap_block_one] other.
Proof.
  intros other other_finalized.
  apply (protocol_projected_execution_finalized_agreement bootstrap_system
    bootstrap_authority bootstrap_honest bootstrap_final_state).
  - reflexivity.
  - exact bootstrap_projected_execution.
  - right. exists bootstrap_certificate. simpl. auto.
  - exact other_finalized.
Qed.

Theorem protocol_nonroot_authority_transition_agreement_inhabited :
  ProjectedExecution bootstrap_system bootstrap_authority bootstrap_honest
      bootstrap_final_state /\
  In bootstrap_reduced_transition
      (safety_authority_transitions bootstrap_final_state) /\
  ConcreteCarrierStep bootstrap_system bootstrap_authority
      [bootstrap_block_one; bootstrap_block_two]
      bootstrap_block_three bootstrap_reduced_transition /\
  transition_signers bootstrap_reduced_transition =
      protocol_block_parent_signers bootstrap_system bootstrap_block_three /\
  SafetyFinalized bootstrap_final_state [bootstrap_block_one] /\
  ChainCompatible [bootstrap_block_one] [bootstrap_block_one].
Proof.
  refine (conj bootstrap_projected_execution _).
  refine (conj _ (conj bootstrap_third_carrier (conj _ _))).
  - simpl. auto.
  - reflexivity.
  - assert (finalized : SafetyFinalized bootstrap_final_state
        [bootstrap_block_one]).
    { right. exists bootstrap_certificate. simpl. auto. }
    split; [exact finalized |].
    exact (bootstrap_nonempty_finality_agrees
      [bootstrap_block_one] finalized).
Qed.

(** * Closed liveness execution *)

Definition liveness_witness_block : Block := mkBlock 1 1 0 1.
Definition liveness_witness_chain : Chain := [liveness_witness_block].
Definition liveness_witness_authority : Authority := [(1, 1)].

Definition liveness_witness_system : ConcreteProtocol :=
  mkConcreteProtocol (fun _ => liveness_witness_authority) (fun _ => [1]).

Definition liveness_witness_inventory :
    CanonicalInventory (fun _ => True).
Proof.
  refine {| inventory_candidates := [liveness_witness_chain];
    inventory_selected := liveness_witness_chain |}.
  - reflexivity.
  - exact I.
  - intros candidate member. simpl in member.
    destruct member as [same | impossible]; [|contradiction].
    subst candidate. rewrite compare_chains_self. discriminate.
Defined.

Definition liveness_witness_observed (_ : nat) : list Chain :=
  inventory_candidates (fun _ => True) liveness_witness_inventory.

Definition liveness_witness_ready :
    ConcreteTarget liveness_witness_system -> Prop :=
  concrete_ready_at liveness_witness_system liveness_witness_authority.

Lemma liveness_witness_delivery :
  EventualDelivery [1] liveness_witness_observed
    (inventory_candidates (fun _ => True) liveness_witness_inventory).
Proof. constructor. intros. reflexivity. Qed.

Lemma liveness_witness_activity :
  ConcreteProtocolActivity liveness_witness_system [1]
    (fun _ _ => True) liveness_witness_ready
    (concrete_base liveness_witness_system
      (inventory_selected (fun _ => True) liveness_witness_inventory)).
Proof.
  apply concrete_protocol_activity_inhabited with
    (authority := liveness_witness_authority).
  - discriminate.
  - intros. reflexivity.
  - intros. reflexivity.
  - reflexivity.
Qed.

Theorem ranked_concrete_protocol_conditional_liveness_inhabited :
  liveness_witness_authority <> [] /\
  exists first second third fourth,
    has_quorum (concrete_authority liveness_witness_system
      (concrete_base liveness_witness_system liveness_witness_chain))
      [1] = true /\
    ConcreteQuorumStep liveness_witness_system [1] (fun _ _ => True)
      (concrete_base liveness_witness_system liveness_witness_chain) first /\
    ConcreteQuorumStep liveness_witness_system [1] (fun _ _ => True)
      first second /\
    ConcreteQuorumStep liveness_witness_system [1] (fun _ _ => True)
      second third /\
    ConcreteQuorumStep liveness_witness_system [1] (fun _ _ => True)
      third fourth /\
    compare_chains (concrete_chain liveness_witness_system first)
      liveness_witness_chain = Lt /\
    q3 (concrete_layers liveness_witness_system third) =
      concrete_layers liveness_witness_system
        (concrete_base liveness_witness_system liveness_witness_chain) /\
    q3 (concrete_layers liveness_witness_system fourth) =
      concrete_layers liveness_witness_system first /\
    exists block,
      concrete_chain liveness_witness_system first =
        liveness_witness_chain ++ [block].
Proof.
  split; [discriminate |].
  pose proof (ranked_concrete_protocol_conditional_liveness
    liveness_witness_system [1] (fun _ _ => True) (fun _ => True)
    liveness_witness_inventory liveness_witness_observed
    liveness_witness_ready liveness_witness_delivery
    liveness_witness_activity) as live.
  destruct live as [first [second [third [fourth live]]]].
  exists first, second, third, fourth.
  unfold liveness_witness_chain in *. simpl in live.
  tauto.
Qed.

(** * Nonvacuous integrated finality-liveness execution *)

Definition liveness_witness_block_two : Block := mkBlock 2 1 1 2.
Definition liveness_witness_block_three : Block := mkBlock 3 1 2 3.
Definition liveness_witness_block_four : Block := mkBlock 4 1 3 4.
Definition liveness_witness_block_five : Block := mkBlock 5 1 4 5.

Definition liveness_witness_child : Chain :=
  [liveness_witness_block; liveness_witness_block_two].

Definition liveness_selected_vote_target : Chain :=
  [liveness_witness_block; liveness_witness_block_two;
   liveness_witness_block_three].

Definition liveness_selected_finality_target : Chain :=
  [liveness_witness_block; liveness_witness_block_two;
   liveness_witness_block_three; liveness_witness_block_four].

Definition liveness_child_finality_target : Chain :=
  [liveness_witness_block; liveness_witness_block_two;
   liveness_witness_block_three; liveness_witness_block_four;
   liveness_witness_block_five].

Definition liveness_execution_transition : CarrierAuthorityTransition :=
  {| transition_parent := liveness_witness_authority;
     transition_child := liveness_witness_authority;
     transition_signers := [1];
     transition_parent_offenders := [];
     transition_child_offenders := [];
     transition_child_from_evidence := eq_refl;
     transition_admitted_by_parent := eq_refl |}.

Lemma liveness_execution_transition_valid :
  AuthorityTransitionValidFrom liveness_witness_authority [1]
    liveness_execution_transition.
Proof. constructor; simpl; intuition congruence. Qed.

Lemma liveness_execution_carrier : forall prefix block,
  ConcreteCarrierStep liveness_witness_system liveness_witness_authority
    prefix block liveness_execution_transition.
Proof.
  intros prefix block. constructor.
  - unfold liveness_execution_transition, liveness_witness_system,
      chain_authority. simpl. destruct (rev prefix); reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma liveness_execution_carrier_trace : forall transitions chain,
  In liveness_execution_transition transitions ->
  ConcreteCarrierTrace liveness_witness_system liveness_witness_authority
    transitions chain.
Proof.
  intros transitions chain stored. induction chain using rev_ind.
  - apply carrier_trace_genesis.
  - apply carrier_trace_append with
      (transition := liveness_execution_transition).
    + exact IHchain.
    + exact stored.
    + apply liveness_execution_carrier.
Qed.

Definition liveness_execution_initial : SafetyState :=
  safety_after_authority genesis_safety_state liveness_execution_transition.

Lemma liveness_execution_initial_trace :
  ProjectedActionTrace liveness_witness_system liveness_witness_authority [1]
    genesis_safety_state liveness_execution_initial.
Proof.
  apply authority_transition_trace.
  exact liveness_execution_transition_valid.
Qed.

Lemma liveness_execution_initial_reachable :
  ProjectedExecution liveness_witness_system liveness_witness_authority [1]
    liveness_execution_initial.
Proof.
  eapply projected_action_trace_extend.
  - exact liveness_execution_initial_trace.
  - apply projected_genesis.
Qed.

Definition liveness_selected_event : SignedTarget :=
  mkSignedTarget 1 1 liveness_selected_vote_target
    [liveness_witness_block; liveness_witness_block_two]
    liveness_witness_chain [].

Lemma liveness_selected_event_computed :
  TargetComputed liveness_witness_system liveness_selected_event.
Proof. constructor; reflexivity. Qed.

Lemma liveness_selected_event_backed :
  EventAuthorityBacked liveness_witness_system liveness_witness_authority
    liveness_execution_initial liveness_selected_event.
Proof.
  unfold EventAuthorityBacked, liveness_execution_initial,
    safety_after_authority. simpl.
  apply liveness_execution_carrier_trace. simpl. auto.
Qed.

Definition liveness_selected_ready : SafetyState :=
  safety_after_vote liveness_execution_initial liveness_selected_event.

Definition liveness_selected_schedule :
  RawVoteSchedule liveness_witness_system liveness_witness_authority [1]
    liveness_execution_initial liveness_selected_ready.
Proof.
  refine (raw_votes_next liveness_witness_system liveness_witness_authority [1]
    liveness_execution_initial liveness_selected_ready liveness_selected_event
    liveness_selected_event_computed liveness_selected_event_backed
    (q3_at_genesis liveness_execution_initial liveness_selected_event eq_refl)
    _ _ _).
  - simpl. intros. contradiction.
  - simpl. intros. contradiction.
  - apply raw_votes_done.
Defined.

Lemma liveness_selected_schedule_events :
  raw_vote_schedule_events liveness_witness_system liveness_witness_authority
    [1] liveness_selected_schedule = [liveness_selected_event].
Proof. reflexivity. Qed.

Definition liveness_selected_vote_delivery :
  HonestVoteDelivery liveness_witness_system liveness_witness_authority [1]
    liveness_execution_initial liveness_witness_chain.
Proof.
  refine
    {| delivery_root := liveness_selected_finality_target;
       delivery_target := liveness_selected_finality_target;
       delivery_finalized_from_q3 := eq_refl;
       delivery_ready := liveness_selected_ready;
       delivery_schedule := liveness_selected_schedule;
       delivery_offenders := [] |}.
  - reflexivity.
  - intros event member. rewrite liveness_selected_schedule_events in member.
    simpl in member. destruct member as [same | impossible].
    + subst event. apply chain_reaches_refl.
    + contradiction.
  - intros event member. rewrite liveness_selected_schedule_events in member.
    simpl in member. destruct member as [same | impossible].
    + subst event. simpl. lia.
    + contradiction.
  - simpl. intuition.
  - reflexivity.
  - left. reflexivity.
Defined.

Definition liveness_selected_after : SafetyState :=
  honest_delivery_after liveness_witness_system liveness_witness_authority [1]
    liveness_execution_initial liveness_witness_chain
    liveness_selected_vote_delivery.

Definition liveness_child_start : SafetyState :=
  safety_after_authority liveness_selected_after liveness_execution_transition.

Definition liveness_child_event : SignedTarget :=
  mkSignedTarget 2 1 liveness_selected_finality_target
    liveness_selected_vote_target liveness_witness_child
    liveness_witness_chain.

Lemma liveness_child_event_computed :
  TargetComputed liveness_witness_system liveness_child_event.
Proof. constructor; reflexivity. Qed.

Lemma liveness_child_event_backed :
  EventAuthorityBacked liveness_witness_system liveness_witness_authority
    liveness_child_start liveness_child_event.
Proof.
  unfold EventAuthorityBacked, liveness_child_start,
    liveness_selected_after, safety_after_authority, honest_delivery_after,
    safety_after_certificate. simpl.
  apply liveness_execution_carrier_trace. simpl. auto.
Qed.

Definition liveness_child_admission :
  Q3Admission liveness_child_start liveness_child_event.
Proof.
  apply q3_from_certificate with
    (certificate := honest_delivery_certificate liveness_witness_system
      liveness_witness_authority [1] liveness_execution_initial
      liveness_witness_chain liveness_selected_vote_delivery).
  - unfold liveness_child_start, liveness_selected_after,
      safety_after_authority, honest_delivery_after,
      safety_after_certificate. simpl. auto.
  - reflexivity.
  - reflexivity.
Defined.

Definition liveness_child_ready : SafetyState :=
  safety_after_vote liveness_child_start liveness_child_event.

Definition liveness_child_schedule :
  RawVoteSchedule liveness_witness_system liveness_witness_authority [1]
    liveness_child_start liveness_child_ready.
Proof.
  refine (raw_votes_next liveness_witness_system liveness_witness_authority [1]
    liveness_child_start liveness_child_ready liveness_child_event
    liveness_child_event_computed liveness_child_event_backed
    liveness_child_admission _ _ _).
  - intros previous member.
    unfold liveness_child_start, liveness_selected_after,
      safety_after_authority, honest_delivery_after,
      safety_after_certificate, liveness_selected_ready,
      safety_after_vote, liveness_execution_initial in member.
    simpl in member. destruct member as [same | impossible].
    + subst previous. simpl. lia.
    + contradiction.
  - intros _ previous member same_signer.
    unfold liveness_child_start, liveness_selected_after,
      safety_after_authority, honest_delivery_after,
      safety_after_certificate, liveness_selected_ready,
      safety_after_vote, liveness_execution_initial in member.
    simpl in member. destruct member as [same | impossible].
    + subst previous. apply signing_descendant.
      exists [liveness_witness_block_four]. reflexivity.
    + contradiction.
  - apply raw_votes_done.
Defined.

Lemma liveness_child_schedule_events :
  raw_vote_schedule_events liveness_witness_system liveness_witness_authority
    [1] liveness_child_schedule = [liveness_child_event].
Proof. reflexivity. Qed.

Definition liveness_child_vote_delivery :
  HonestVoteDelivery liveness_witness_system liveness_witness_authority [1]
    liveness_child_start liveness_witness_child.
Proof.
  refine
    {| delivery_root := liveness_child_finality_target;
       delivery_target := liveness_child_finality_target;
       delivery_finalized_from_q3 := eq_refl;
       delivery_ready := liveness_child_ready;
       delivery_schedule := liveness_child_schedule;
       delivery_offenders := [] |}.
  - reflexivity.
  - intros event member. rewrite liveness_child_schedule_events in member.
    simpl in member. destruct member as [same | impossible].
    + subst event. apply chain_reaches_refl.
    + contradiction.
  - intros event member. rewrite liveness_child_schedule_events in member.
    simpl in member. destruct member as [same | impossible].
    + subst event. simpl. lia.
    + contradiction.
  - simpl. intuition.
  - reflexivity.
  - left. reflexivity.
Defined.

Definition liveness_finality_activity :
  ContinuedHonestActivity liveness_witness_system liveness_witness_authority [1]
    liveness_execution_initial liveness_witness_chain (fun _ => True).
Proof.
  refine
    {| selected_delivery := liveness_selected_vote_delivery;
       descendant_block := liveness_witness_block_two;
       descendant_transition := liveness_execution_transition;
       descendant := liveness_witness_child;
       descendant_exact_child := eq_refl;
       descendant_valid := I;
       descendant_carrier := liveness_execution_carrier
         liveness_witness_chain liveness_witness_block_two;
       descendant_authority_valid := liveness_execution_transition_valid;
       descendant_delivery := liveness_child_vote_delivery |}.
Defined.

Definition liveness_finality_result :
  ProtocolLivenessResult liveness_witness_system liveness_witness_authority [1]
    liveness_execution_initial (fun _ => True) liveness_witness_inventory
    liveness_witness_observed :=
  ranked_protocol_conditional_finality_liveness liveness_witness_system
    liveness_witness_authority [1] liveness_execution_initial (fun _ => True)
    liveness_witness_inventory liveness_witness_observed eq_refl
    liveness_execution_initial_reachable liveness_witness_delivery
    liveness_finality_activity.

Theorem ranked_protocol_conditional_finality_liveness_inhabited :
  liveness_witness_authority <> [] /\
  liveness_witness_chain <> [] /\
  result_descendant liveness_witness_system liveness_witness_authority [1]
    liveness_execution_initial (fun _ => True) liveness_witness_inventory
    liveness_witness_observed liveness_finality_result <> [] /\
  ProjectedExecution liveness_witness_system liveness_witness_authority [1]
    (result_final_state liveness_witness_system liveness_witness_authority [1]
      liveness_execution_initial (fun _ => True) liveness_witness_inventory
      liveness_witness_observed liveness_finality_result) /\
  SafetyFinalized
    (result_final_state liveness_witness_system liveness_witness_authority [1]
      liveness_execution_initial (fun _ => True) liveness_witness_inventory
      liveness_witness_observed liveness_finality_result)
    liveness_witness_chain /\
  SafetyFinalized
    (result_final_state liveness_witness_system liveness_witness_authority [1]
      liveness_execution_initial (fun _ => True) liveness_witness_inventory
      liveness_witness_observed liveness_finality_result)
    (result_descendant liveness_witness_system liveness_witness_authority [1]
      liveness_execution_initial (fun _ => True) liveness_witness_inventory
      liveness_witness_observed liveness_finality_result) /\
  (exists block,
    result_descendant liveness_witness_system liveness_witness_authority [1]
      liveness_execution_initial (fun _ => True) liveness_witness_inventory
      liveness_witness_observed liveness_finality_result =
      liveness_witness_chain ++ [block]) /\
  (exists block transition,
    result_descendant liveness_witness_system liveness_witness_authority [1]
      liveness_execution_initial (fun _ => True) liveness_witness_inventory
      liveness_witness_observed liveness_finality_result =
      liveness_witness_chain ++ [block] /\
    ConcreteCarrierStep liveness_witness_system liveness_witness_authority
      liveness_witness_chain block transition /\
    AuthorityTransitionValidFrom liveness_witness_authority [1] transition) /\
  ChainCompatible liveness_witness_chain
    (result_descendant liveness_witness_system liveness_witness_authority [1]
      liveness_execution_initial (fun _ => True) liveness_witness_inventory
      liveness_witness_observed liveness_finality_result).
Proof.
  repeat split.
  - discriminate.
  - discriminate.
  - change (liveness_witness_child <> []). discriminate.
  - exact (result_execution liveness_witness_system
      liveness_witness_authority [1] liveness_execution_initial
      (fun _ => True) liveness_witness_inventory liveness_witness_observed
      liveness_finality_result).
  - exact (result_selected_finalized liveness_witness_system
      liveness_witness_authority [1] liveness_execution_initial
      (fun _ => True) liveness_witness_inventory liveness_witness_observed
      liveness_finality_result).
  - exact (result_descendant_finalized liveness_witness_system
      liveness_witness_authority [1] liveness_execution_initial
      (fun _ => True) liveness_witness_inventory liveness_witness_observed
      liveness_finality_result).
  - exact (result_exact_child liveness_witness_system
      liveness_witness_authority [1] liveness_execution_initial
      (fun _ => True) liveness_witness_inventory liveness_witness_observed
      liveness_finality_result).
  - exact (result_valid_carrier liveness_witness_system
      liveness_witness_authority [1] liveness_execution_initial
      (fun _ => True) liveness_witness_inventory liveness_witness_observed
      liveness_finality_result).
  - exact (result_finalized_compatible liveness_witness_system
      liveness_witness_authority [1] liveness_execution_initial
      (fun _ => True) liveness_witness_inventory liveness_witness_observed
      liveness_finality_result).
Qed.
