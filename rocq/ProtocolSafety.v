From Coq Require Import List Arith Bool Lia Wf_nat.
From BFT Require Import Protocol ConcreteProtocol Quorum Ranking CatchupSafety.
Import ListNotations.

(** * Ranked proposal and catch-up admission *)

(** A vote stores the exact three frontiers computed when it was signed. *)
Record SignedTarget := mkSignedTarget {
  signed_time : nat;
  signed_signer : nat;
  signed_target : Chain;
  signed_q1 : Chain;
  signed_q2 : Chain;
  signed_q3 : Chain
}.

Record TargetComputed (system : ConcreteProtocol) (event : SignedTarget) : Prop := {
  computed_q1 : signed_q1 event = protocol_frontier system (signed_target event);
  computed_q2 : signed_q2 event = protocol_frontier system (signed_q1 event);
  computed_q3 : signed_q3 event = protocol_frontier system (signed_q2 event)
}.

(** The three alternatives used by the ranked proposal guard. *)
Definition ProposalGuard (current previous : SignedTarget) : Prop :=
  chain_reaches (signed_q1 previous) (signed_q1 current) \/
  chain_reaches (signed_q2 previous) (signed_q2 current) \/
  (chain_reaches (signed_q2 previous) (signed_q1 current) /\
    ~ (signed_q1 previous <> signed_q2 current /\
      chain_reaches (signed_q2 current) (signed_q1 previous))).

Record RankedProposalGuard (current previous : SignedTarget) : Prop := {
  ranked_guard_selection : RankedSwitch
    (signed_target previous) (signed_target current);
  ranked_guard_frontiers : ProposalGuard current previous
}.

Lemma proposal_guard_preserves_q2 : forall system current previous,
  TargetComputed system current -> TargetComputed system previous ->
  ProposalGuard current previous ->
  chain_reaches (signed_q2 previous) (signed_q2 current).
Proof.
  intros system current previous current_computed previous_computed guard.
  destruct current_computed as [current_q1 current_q2 current_q3].
  destruct previous_computed as [previous_q1 previous_q2 previous_q3].
  destruct guard as [q1_nonretreating | [q2_nonretreating | one_sided]].
  - rewrite previous_q2, current_q2.
    now apply protocol_frontier_monotone.
  - exact q2_nonretreating.
  - destruct one_sided as [previous_q2_below_current_q1 no_reverse].
    assert (current_q2_below_current_q1 :
        chain_reaches (signed_q2 current) (signed_q1 current)).
    { rewrite current_q2. apply protocol_frontier_below. }
    destruct (chain_ancestors_comparable
        (signed_q2 current) (signed_q2 previous) (signed_q1 current)
        current_q2_below_current_q1 previous_q2_below_current_q1)
      as [current_to_previous | previous_to_current].
    + destruct (chain_eq_dec (signed_q1 previous) (signed_q2 current))
        as [boundary | distinct].
      * rewrite <- boundary, previous_q2.
        apply protocol_frontier_below.
      * exfalso. apply no_reverse. split.
        -- exact distinct.
        -- eapply chain_reaches_trans.
           ++ exact current_to_previous.
           ++ rewrite previous_q2. apply protocol_frontier_below.
    + exact previous_to_current.
Qed.

(** The derived safety content of two ordered votes by one honest signer. *)
Inductive CertifiedRankLE : SignedTarget -> SignedTarget -> Prop :=
| certified_q2_retained : forall older newer,
    chain_reaches (signed_q2 older) (signed_q2 newer) ->
    CertifiedRankLE older newer
| certified_q3_catchup : forall older newer,
    chain_reaches (signed_q3 older) (signed_q3 newer) ->
    length (signed_q2 older) <= length (signed_q3 newer) ->
    CertifiedRankLE older newer.


(** * Certificates and concrete protocol steps *)

Record ProtocolCertificate := mkProtocolCertificate {
  protocol_finalized : Chain;
  protocol_lock : Chain;
  protocol_covered : chain_reaches protocol_finalized protocol_lock;
  protocol_root : Chain;
  protocol_contributors : list SignedTarget;
  protocol_offenders : list nat;
  contributor_covers : forall event,
    In event protocol_contributors ->
    chain_reaches protocol_lock (signed_q2 event);
  contributor_below_root : forall event,
    In event protocol_contributors ->
    length (signed_target event) < length protocol_root
}.

Definition certificate_signers (certificate : ProtocolCertificate) : list nat :=
  map signed_signer (protocol_contributors certificate).

Definition protocol_covered_certificate (certificate : ProtocolCertificate) :
    CoveredCertificate chain_reaches :=
  {| certificate_finalized := protocol_finalized certificate;
     certificate_lock := protocol_lock certificate;
     certificate_covered := protocol_covered certificate |}.

Record SafetyState := mkSafetyState {
  safety_events : list SignedTarget;
  safety_certificates : list ProtocolCertificate;
  safety_authority_transitions : list CarrierAuthorityTransition
}.

Definition genesis_safety_state : SafetyState := mkSafetyState [] [] [].

(** Every Block in an emitted target is backed by a checked transition for its
    exact preceding chain prefix. *)
Definition EventAuthorityBacked
    (system : ConcreteProtocol) (root : Authority)
    (state : SafetyState) (event : SignedTarget) : Prop :=
  ConcreteCarrierTrace system root
    (safety_authority_transitions state) (signed_target event).

(** A certificate's offender-reduced authority is similarly tied to the root
    or to a transition already recorded before certificate admission. *)
Definition CertificateAuthorityBacked
    (system : ConcreteProtocol) (root : Authority) (state : SafetyState)
    (certificate : ProtocolCertificate) : Prop :=
  after_evidence root (protocol_offenders certificate) = root \/
  exists event transition,
    In event (protocol_contributors certificate) /\
    In transition (safety_authority_transitions state) /\
    ConcreteCarrierInChain system root (signed_target event) transition /\
    transition_child transition =
      after_evidence root (protocol_offenders certificate).

Record CertificateValidIn
    (authority : Authority) (honest : list nat)
    (events : list SignedTarget) (certificate : ProtocolCertificate) : Prop := {
  valid_contributors_stored : forall event,
    In event (protocol_contributors certificate) -> In event events;
  valid_offenders_safe : forall offender,
    In offender (protocol_offenders certificate) -> ~ In offender honest;
  valid_contributor_quorum :
    has_quorum (after_evidence authority (protocol_offenders certificate))
      (certificate_signers certificate) = true
}.

Definition chain_reachesb (ancestor descendant : Chain) : bool :=
  if chain_eq_dec (firstn (length ancestor) descendant) ancestor
  then Nat.leb (length ancestor) (length descendant)
  else false.

Lemma chain_reachesb_true : forall ancestor descendant,
  chain_reachesb ancestor descendant = true -> chain_reaches ancestor descendant.
Proof.
  intros ancestor descendant checked. unfold chain_reachesb in checked.
  destruct (chain_eq_dec (firstn (length ancestor) descendant) ancestor)
    as [prefix | not_prefix]; [|discriminate].
  apply Nat.leb_le in checked. exists (skipn (length ancestor) descendant).
  pose proof (firstn_skipn (length ancestor) descendant) as split_at_ancestor.
  rewrite prefix in split_at_ancestor. symmetry. exact split_at_ancestor.
Qed.

(** Every non-genesis Q3 names a certificate already stored by the receiver.
    The root-height comparison is an executable check on that same object. *)
Inductive Q3Admission (before : SafetyState) (event : SignedTarget) : Type :=
| q3_at_genesis :
    signed_q3 event = [] -> Q3Admission before event
| q3_from_certificate : forall certificate,
    In certificate (safety_certificates before) ->
    protocol_lock certificate = signed_q3 event ->
    Nat.leb (length (protocol_root certificate))
      (length (signed_target event)) = true ->
    Q3Admission before event.

(** Certified catch-up adds two executable checks to a non-genesis Q3
    admission. It cannot be constructed from a genesis admission. *)
Definition AcceptedCatchup
    (before : SafetyState) (current previous : SignedTarget)
    (admission : Q3Admission before current) : Prop :=
  match admission with
  | q3_at_genesis _ _ _ => False
  | q3_from_certificate _ _ certificate _ _ _ =>
      chain_reachesb (signed_q3 previous) (protocol_lock certificate) = true /\
      Nat.leb (length (signed_q2 previous))
        (length (protocol_lock certificate)) = true
  end.

(** Exactly the three transition classes accepted before an honest vote. *)
Inductive LocalSigningTransition (before : SafetyState) :
    forall current, Q3Admission before current -> SignedTarget -> Prop :=
| signing_descendant : forall current previous,
    chain_reaches (signed_target previous) (signed_target current) ->
    forall admission,
      LocalSigningTransition before current admission previous
| signing_ranked : forall current previous,
    RankedProposalGuard current previous ->
    forall admission,
      LocalSigningTransition before current admission previous
| signing_certified_catchup : forall current previous,
    forall admission,
      AcceptedCatchup before current previous admission ->
      LocalSigningTransition before current admission previous.

Lemma signing_transition_certified_rank_le :
  forall system before current admission previous,
    TargetComputed system current -> TargetComputed system previous ->
    LocalSigningTransition before current admission previous ->
    CertifiedRankLE previous current.
Proof.
  intros system before current admission previous
    current_computed previous_computed transition.
  destruct transition as
      [current previous descendant admission |
       current previous ranked_guard admission |
       current previous admission catchup].
  - destruct current_computed as [current_q1 current_q2 current_q3].
    destruct previous_computed as [previous_q1 previous_q2 previous_q3].
    apply certified_q2_retained.
    rewrite previous_q2, current_q2, previous_q1, current_q1.
    apply protocol_frontier_monotone.
    now apply protocol_frontier_monotone.
  - apply certified_q2_retained.
    apply proposal_guard_preserves_q2 with (system := system); try assumption.
    exact (ranked_guard_frontiers current previous ranked_guard).
  - destruct admission as [at_genesis | certificate accepted current_locked root_checked].
    + contradiction.
    + simpl in catchup. destruct catchup as [q3_checked height_checked].
      apply certified_q3_catchup.
      * rewrite <- current_locked. now apply chain_reachesb_true.
      * rewrite <- current_locked. now apply Nat.leb_le.
Qed.

Definition SigningHistory (honest : list nat) (events : list SignedTarget) : Prop :=
  forall older, In older events -> forall newer, In newer events ->
    In (signed_signer older) honest ->
    signed_signer older = signed_signer newer ->
    signed_time older <= signed_time newer ->
    CertifiedRankLE older newer.

Inductive SafetyStep (system : ConcreteProtocol)
    (authority : Authority) (honest : list nat) :
    SafetyState -> SafetyState -> Type :=
| safety_stutter : forall state, SafetyStep system authority honest state state
| safety_admit_certificate : forall before certificate,
    CertificateValidIn authority honest (safety_events before) certificate ->
    CertificateAuthorityBacked system authority before certificate ->
    SafetyStep system authority honest before
      (mkSafetyState (safety_events before)
        (safety_certificates before ++ [certificate])
        (safety_authority_transitions before))
| safety_emit_vote : forall before event,
    TargetComputed system event ->
    EventAuthorityBacked system authority before event ->
    forall admission : Q3Admission before event,
    (forall previous, In previous (safety_events before) ->
      signed_time previous < signed_time event) ->
    (In (signed_signer event) honest -> forall previous,
      In previous (safety_events before) ->
      signed_signer previous = signed_signer event ->
      LocalSigningTransition before event admission previous) ->
    SafetyStep system authority honest before
      (mkSafetyState (safety_events before ++ [event])
        (safety_certificates before)
        (safety_authority_transitions before))
| safety_apply_authority : forall before transition,
    AuthorityTransitionValidFrom authority honest transition ->
    SafetyStep system authority honest before
      (mkSafetyState (safety_events before)
        (safety_certificates before)
        (safety_authority_transitions before ++ [transition])).

(** * Seven-action projection *)

Inductive SafetyEffects (system : ConcreteProtocol)
    (authority : Authority) (honest : list nat) :
    SafetyState -> SafetyState -> Type :=
| effects_done : forall state, SafetyEffects system authority honest state state
| effects_next : forall before middle after,
    SafetyStep system authority honest before middle ->
    SafetyEffects system authority honest middle after ->
    SafetyEffects system authority honest before after.

Fixpoint effects_emitted_votes
    (system : ConcreteProtocol) (authority : Authority) (honest : list nat)
    {before after : SafetyState}
    (effects : SafetyEffects system authority honest before after) : nat :=
  match effects with
  | effects_done _ _ _ _ => 0
  | effects_next _ _ _ _ _ _ first rest =>
      (match first with safety_emit_vote _ _ _ _ _ _ _ _ _ _ => 1 | _ => 0 end) +
      effects_emitted_votes system authority honest rest
  end.

Inductive SafetyEffectClass :=
| effect_stutter
| effect_admit_certificate
| effect_emit_vote
| effect_apply_authority.

Definition safety_step_class
    (system : ConcreteProtocol) (authority : Authority) (honest : list nat)
    {before after : SafetyState}
    (step : SafetyStep system authority honest before after) : SafetyEffectClass :=
  match step with
  | safety_stutter _ _ _ _ => effect_stutter
  | safety_admit_certificate _ _ _ _ _ _ _ => effect_admit_certificate
  | safety_emit_vote _ _ _ _ _ _ _ _ _ _ => effect_emit_vote
  | safety_apply_authority _ _ _ _ _ _ => effect_apply_authority
  end.

(** Sign/propose actions may only emit durable votes; delivery actions may
    only accept checked certificates or checked authority changes. *)
Definition action_allows_effect
    (kind : ActionKind) (effect : SafetyEffectClass) : Prop :=
  match kind, effect with
  | SignVote, effect_stutter
  | SignVote, effect_emit_vote
  | Propose, effect_stutter
  | Propose, effect_emit_vote
  | DeliverVote, effect_stutter
  | DeliverVote, effect_admit_certificate
  | DeliverVote, effect_apply_authority
  | DeliverProposal, effect_stutter
  | DeliverProposal, effect_admit_certificate
  | DeliverProposal, effect_apply_authority => True
  | _, _ => False
  end.

Fixpoint effects_allowed
    (system : ConcreteProtocol) (authority : Authority) (honest : list nat)
    (kind : ActionKind) {before after : SafetyState}
    (effects : SafetyEffects system authority honest before after) : Prop :=
  match effects with
  | effects_done _ _ _ _ => True
  | effects_next _ _ _ _ _ _ first rest =>
      action_allows_effect kind
        (safety_step_class system authority honest first) /\
      effects_allowed system authority honest kind rest
  end.

Inductive ProjectedAction (system : ConcreteProtocol)
    (authority : Authority) (honest : list nat) :
    SafetyState -> SafetyState -> Type :=
| projected_sign_vote : forall before after
    (effects : SafetyEffects system authority honest before after),
    effects_allowed system authority honest SignVote effects ->
    effects_emitted_votes system authority honest effects <=
      action_limit SignVote ->
    ProjectedAction system authority honest before after
| projected_propose : forall before after
    (effects : SafetyEffects system authority honest before after),
    effects_allowed system authority honest Propose effects ->
    effects_emitted_votes system authority honest effects <=
      action_limit Propose ->
    ProjectedAction system authority honest before after
| projected_publish_vote : forall state,
    ProjectedAction system authority honest state state
| projected_publish_proposal : forall state,
    ProjectedAction system authority honest state state
| projected_deliver_vote : forall before after
    (effects : SafetyEffects system authority honest before after),
    effects_allowed system authority honest DeliverVote effects ->
    effects_emitted_votes system authority honest effects <=
      action_limit DeliverVote ->
    ProjectedAction system authority honest before after
| projected_deliver_proposal : forall before after
    (effects : SafetyEffects system authority honest before after),
    effects_allowed system authority honest DeliverProposal effects ->
    effects_emitted_votes system authority honest effects <=
      action_limit DeliverProposal ->
    ProjectedAction system authority honest before after
| projected_idle : forall state,
    ProjectedAction system authority honest state state.

Definition ProjectedActionEffects
    (system : ConcreteProtocol) (authority : Authority) (honest : list nat)
    (before after : SafetyState)
    (action : ProjectedAction system authority honest before after) :
    SafetyEffects system authority honest before after :=
  match action with
  | projected_sign_vote _ _ _ _ _ effects _ _ => effects
  | projected_propose _ _ _ _ _ effects _ _ => effects
  | projected_publish_vote _ _ _ state =>
      effects_done system authority honest state
  | projected_publish_proposal _ _ _ state =>
      effects_done system authority honest state
  | projected_deliver_vote _ _ _ _ _ effects _ _ => effects
  | projected_deliver_proposal _ _ _ _ _ effects _ _ => effects
  | projected_idle _ _ _ state => effects_done system authority honest state
  end.

Definition ProjectedActionKind
    (system : ConcreteProtocol) (authority : Authority) (honest : list nat)
    {before after : SafetyState}
    (action : ProjectedAction system authority honest before after) : ActionKind :=
  match action with
  | projected_sign_vote _ _ _ _ _ _ _ _ => SignVote
  | projected_propose _ _ _ _ _ _ _ _ => Propose
  | projected_publish_vote _ _ _ _ => PublishVote
  | projected_publish_proposal _ _ _ _ => PublishProposal
  | projected_deliver_vote _ _ _ _ _ _ _ _ => DeliverVote
  | projected_deliver_proposal _ _ _ _ _ _ _ _ => DeliverProposal
  | projected_idle _ _ _ _ => Idle
  end.

Lemma projected_action_emission_bound :
  forall system authority honest before after
    (action : ProjectedAction system authority honest before after),
    effects_emitted_votes system authority honest
      (ProjectedActionEffects system authority honest before after action) <=
    action_limit (ProjectedActionKind system authority honest action).
Proof. intros. destruct action; simpl in *; auto. Qed.

Inductive ProjectedExecution (system : ConcreteProtocol)
    (authority : Authority) (honest : list nat) :
    SafetyState -> Prop :=
| projected_genesis :
    ProjectedExecution system authority honest genesis_safety_state
| projected_action : forall before after,
    ProjectedExecution system authority honest before ->
    ProjectedAction system authority honest before after ->
    ProjectedExecution system authority honest after.

Inductive StrongReachable (system : ConcreteProtocol)
    (authority : Authority) (honest : list nat) :
    SafetyState -> Prop :=
| strong_genesis : StrongReachable system authority honest genesis_safety_state
| strong_step : forall before after,
    StrongReachable system authority honest before ->
    SafetyStep system authority honest before after ->
    StrongReachable system authority honest after.

(** * Reachability invariants *)

Record SafetyConsistent
    (system : ConcreteProtocol) (authority : Authority)
    (honest : list nat) (state : SafetyState) : Prop := {
  consistent_targets_computed : forall event,
    In event (safety_events state) -> TargetComputed system event;
  consistent_event_authorities : forall event,
    In event (safety_events state) ->
    EventAuthorityBacked system authority state event;
  consistent_signing_history : SigningHistory honest (safety_events state);
  consistent_certificates : forall certificate,
    In certificate (safety_certificates state) ->
    CertificateValidIn authority honest (safety_events state) certificate;
  consistent_certificate_authorities : forall certificate,
    In certificate (safety_certificates state) ->
    CertificateAuthorityBacked system authority state certificate;
  consistent_q3_covered : forall event,
    In event (safety_events state) ->
    signed_q3 event <> [] ->
    exists certificate,
      In certificate (safety_certificates state) /\
      protocol_lock certificate = signed_q3 event /\
      length (protocol_root certificate) <= length (signed_target event);
  consistent_authority_transitions : forall transition,
    In transition (safety_authority_transitions state) ->
    AuthorityTransitionValidFrom authority honest transition
}.

Definition SafetyFinalized (state : SafetyState) (chain : Chain) : Prop :=
  chain = [] \/ exists certificate,
    In certificate (safety_certificates state) /\
    protocol_finalized certificate = chain.

Lemma certificate_valid_mono : forall authority honest older newer certificate,
  CertificateValidIn authority honest older certificate ->
  (forall event, In event older -> In event newer) ->
  CertificateValidIn authority honest newer certificate.
Proof.
  intros authority honest older newer certificate valid subset.
  destruct valid as [stored safe quorum].
  constructor; eauto.
Qed.

Lemma event_authority_backed_mono :
  forall system authority older newer event,
    EventAuthorityBacked system authority older event ->
    (forall transition,
      In transition (safety_authority_transitions older) ->
      In transition (safety_authority_transitions newer)) ->
    EventAuthorityBacked system authority newer event.
Proof.
  intros system authority older newer event backed subset.
  eapply concrete_carrier_trace_mono; eauto.
Qed.

Lemma certificate_authority_backed_mono :
  forall system authority older newer certificate,
    CertificateAuthorityBacked system authority older certificate ->
    (forall transition,
      In transition (safety_authority_transitions older) ->
      In transition (safety_authority_transitions newer)) ->
    CertificateAuthorityBacked system authority newer certificate.
Proof.
  intros system authority older newer certificate backed subset.
  destruct backed as
    [root | [event [transition [contributor [stored [carrier child]]]]]].
  - now left.
  - right. exists event, transition. repeat split; auto.
Qed.

Lemma safety_step_preserves_consistency : forall system authority honest before after,
  SafetyStep system authority honest before after ->
  SafetyConsistent system authority honest before ->
  SafetyConsistent system authority honest after.
Proof.
  intros system authority honest before after step consistent.
  destruct consistent as
      [computed event_authorities history certificates
       certificate_authorities q3_covered authorities].
  destruct step as
      [state | before certificate valid certificate_authority |
       before event event_computed event_authority admission fresh classified |
       before transition transition_valid].
  - constructor; assumption.
  - constructor.
    + exact computed.
    + exact event_authorities.
    + exact history.
    + simpl. intros candidate member.
      apply in_app_iff in member. destruct member as [old | added].
      * exact (certificates candidate old).
      * simpl in added. destruct added as [same | impossible].
        -- subst candidate. exact valid.
        -- contradiction.
    + simpl. intros candidate member.
      apply in_app_iff in member. destruct member as [old | added].
      * exact (certificate_authorities candidate old).
      * simpl in added. destruct added as [same | impossible].
        -- subst candidate. exact certificate_authority.
        -- contradiction.
    + intros event stored nonempty.
      destruct (q3_covered event stored nonempty)
        as [candidate [candidate_member [locked bound]]].
      exists candidate. split.
      * apply in_app_iff. left. exact candidate_member.
      * auto.
    + exact authorities.
  - constructor.
    + simpl. intros candidate member.
      apply in_app_iff in member. destruct member as [old | added].
      * exact (computed candidate old).
      * simpl in added. destruct added as [same | impossible].
        -- subst candidate. exact event_computed.
        -- contradiction.
    + simpl. intros candidate member.
      apply in_app_iff in member. destruct member as [old | added].
      * exact (event_authorities candidate old).
      * simpl in added. destruct added as [same | impossible].
        -- subst candidate. exact event_authority.
        -- contradiction.
    + unfold SigningHistory in *. simpl.
      intros older older_member newer newer_member older_honest same_signer order.
      apply in_app_iff in older_member. apply in_app_iff in newer_member.
      destruct older_member as [older_old | older_new];
        destruct newer_member as [newer_old | newer_new].
      * exact (history older older_old newer newer_old older_honest
          same_signer order).
      * simpl in newer_new. destruct newer_new as [newer_equal | impossible].
        -- subst newer. apply signing_transition_certified_rank_le with
             (system := system) (before := before) (admission := admission).
           ++ exact event_computed.
           ++ exact (computed older older_old).
           ++ apply classified.
              ** rewrite <- same_signer. exact older_honest.
              ** exact older_old.
              ** exact same_signer.
        -- contradiction.
      * simpl in older_new. destruct older_new as [older_equal | impossible].
        -- subst older. pose proof (fresh newer newer_old). lia.
        -- contradiction.
      * simpl in older_new, newer_new.
        destruct older_new as [older_equal | impossible]; [|contradiction].
        destruct newer_new as [newer_equal | impossible]; [|contradiction].
        subst older. subst newer.
        apply certified_q2_retained.
        apply chain_reaches_refl.
    + simpl. intros certificate member.
      apply certificate_valid_mono with (older := safety_events before).
      * exact (certificates certificate member).
      * intros previous previous_member.
        apply in_app_iff. left. exact previous_member.
    + exact certificate_authorities.
    + simpl. intros candidate member nonempty.
      apply in_app_iff in member. destruct member as [old | added].
      * exact (q3_covered candidate old nonempty).
      * simpl in added. destruct added as [same | impossible].
        -- subst candidate.
           destruct admission as
               [at_genesis | certificate accepted locked root_checked].
           ++ contradiction.
           ++ exists certificate. split; [exact accepted |].
              split; [exact locked |]. now apply Nat.leb_le.
        -- contradiction.
    + exact authorities.
  - constructor.
    + exact computed.
    + intros event stored.
      eapply event_authority_backed_mono.
      * exact (event_authorities event stored).
      * simpl. intros candidate member. apply in_app_iff. now left.
    + exact history.
    + exact certificates.
    + intros certificate stored.
      eapply certificate_authority_backed_mono.
      * exact (certificate_authorities certificate stored).
      * simpl. intros candidate member. apply in_app_iff. now left.
    + exact q3_covered.
    + simpl. intros candidate member.
      apply in_app_iff in member. destruct member as [old | added].
      * exact (authorities candidate old).
      * simpl in added. destruct added as [same | impossible].
        -- subst candidate. exact transition_valid.
        -- contradiction.
Qed.

Lemma strong_reachable_consistent : forall system authority honest state,
  StrongReachable system authority honest state ->
  SafetyConsistent system authority honest state.
Proof.
  intros system authority honest state reachable.
  induction reachable as [|before after earlier step IH].
  - constructor.
    + simpl. intros. contradiction.
    + simpl. intros. contradiction.
    + unfold SigningHistory. simpl. intros. contradiction.
    + simpl. intros. contradiction.
    + simpl. intros. contradiction.
    + simpl. intros. contradiction.
    + simpl. intros. contradiction.
  - eapply safety_step_preserves_consistency; eauto.
Qed.

Lemma effects_preserve_reachable : forall system authority honest before after,
  SafetyEffects system authority honest before after ->
  StrongReachable system authority honest before ->
  StrongReachable system authority honest after.
Proof.
  intros system authority honest before after effects reachable.
  induction effects as [state | before middle after first rest IH].
  - exact reachable.
  - apply IH.
    exact (strong_step system authority honest before middle reachable first).
Qed.

Lemma projected_action_preserves_reachable :
  forall system authority honest before after,
  ProjectedAction system authority honest before after ->
  StrongReachable system authority honest before ->
  StrongReachable system authority honest after.
Proof.
  intros system authority honest before after action reachable.
  apply (effects_preserve_reachable system authority honest before after
    (ProjectedActionEffects system authority honest before after action)
    reachable).
Qed.

Lemma projected_execution_reachable : forall system authority honest state,
  ProjectedExecution system authority honest state ->
  StrongReachable system authority honest state.
Proof.
  intros system authority honest state execution.
  induction execution as [|before after earlier action IH].
  - apply strong_genesis.
  - exact (projected_action_preserves_reachable system authority honest
      before after IH action).
Qed.

(** * Finalized agreement *)

Lemma chain_compatible_sym : forall left right,
  ChainCompatible left right -> ChainCompatible right left.
Proof.
  intros left right compatible. destruct compatible as [forward | reverse].
  - right. exact forward.
  - left. exact reverse.
Qed.

Lemma covered_certificates_agree : forall left right,
  ChainCompatible (protocol_lock left) (protocol_lock right) ->
  ChainCompatible (protocol_finalized left) (protocol_finalized right).
Proof.
  intros left right locks. destruct locks as [left_to_right | right_to_left].
  - exact (certificate_covered_catchup_safety Chain chain_reaches
      chain_reaches_trans chain_ancestors_comparable
      (protocol_covered_certificate left) (protocol_covered_certificate right)
      (protocol_lock right) left_to_right (chain_reaches_refl _)).
  - exact (certificate_covered_catchup_safety Chain chain_reaches
      chain_reaches_trans chain_ancestors_comparable
      (protocol_covered_certificate left) (protocol_covered_certificate right)
      (protocol_lock left) (chain_reaches_refl _) right_to_left).
Qed.

Lemma ordered_certificate_locks_agree :
  forall system authority honest state bound older newer older_event newer_event,
    SafetyConsistent system authority honest state ->
    In older (safety_certificates state) ->
    In newer (safety_certificates state) ->
    In older_event (protocol_contributors older) ->
    In newer_event (protocol_contributors newer) ->
    CertifiedRankLE older_event newer_event ->
    length (protocol_root older) + length (protocol_root newer) <= bound ->
    (forall pivot,
      In pivot (safety_certificates state) ->
      length (protocol_root older) + length (protocol_root pivot) < bound ->
      ChainCompatible (protocol_lock older) (protocol_lock pivot)) ->
    ChainCompatible (protocol_lock older) (protocol_lock newer).
Proof.
  intros system authority honest state bound older newer older_event newer_event
    consistent older_accepted newer_accepted older_member newer_member ordered
    root_bound recurse.
  destruct consistent as
    [computed event_authorities history certificates certificate_authorities
     q3_covered authorities].
  pose proof (certificates older older_accepted) as older_valid.
  pose proof (certificates newer newer_accepted) as newer_valid.
  destruct older_valid as [older_stored older_safe older_quorum].
  destruct newer_valid as [newer_stored newer_safe newer_quorum].
  destruct ordered as
      [older_event newer_event q2_retained |
       older_event newer_event q3_retained certified_height].
  - assert (locks_common :
        ChainCompatible (protocol_lock older) (protocol_lock newer)).
    { apply chain_ancestors_comparable with (tip := signed_q2 newer_event).
      - eapply chain_reaches_trans.
        + exact (contributor_covers older older_event older_member).
        + exact q2_retained.
      - exact (contributor_covers newer newer_event newer_member). }
    exact locks_common.
  - assert (locked_height :
        length (protocol_lock older) <= length (signed_q3 newer_event)).
    { eapply Nat.le_trans.
      - apply chain_reaches_length.
        exact (contributor_covers older older_event older_member).
      - exact certified_height. }
    assert (older_to_q3 :
        chain_reaches (protocol_lock older) (signed_q3 newer_event)).
    { destruct (chain_eq_dec (signed_q3 newer_event) [])
        as [at_genesis | nonempty].
      - assert (older_empty : protocol_lock older = []).
        { apply length_zero_iff_nil.
          rewrite at_genesis in locked_height. simpl in locked_height. lia. }
        rewrite older_empty. exists (signed_q3 newer_event). reflexivity.
      - destruct (q3_covered newer_event
          (newer_stored newer_event newer_member) nonempty)
          as [pivot [pivot_accepted [pivot_locked pivot_bound]]].
        assert (smaller :
            length (protocol_root older) + length (protocol_root pivot) < bound).
        { pose proof (contributor_below_root newer newer_event newer_member).
          lia. }
        destruct (recurse pivot pivot_accepted smaller)
          as [older_to_pivot | pivot_to_older].
        + rewrite pivot_locked in older_to_pivot. exact older_to_pivot.
        + assert (pivot_height :
              length (protocol_lock pivot) <= length (protocol_lock older)).
          { apply chain_reaches_length. exact pivot_to_older. }
          assert (older_height :
              length (protocol_lock older) <= length (protocol_lock pivot)).
          { rewrite pivot_locked. exact locked_height. }
          assert (same_height :
              length (protocol_lock pivot) = length (protocol_lock older)) by lia.
          pose proof (chain_reaches_same_length _ _ pivot_to_older same_height)
            as same_lock.
          rewrite <- same_lock, pivot_locked. apply chain_reaches_refl. }
    apply chain_ancestors_comparable with (tip := signed_q2 newer_event).
    + eapply chain_reaches_trans.
      * exact older_to_q3.
      * pose proof (computed newer_event
          (newer_stored newer_event newer_member)) as newer_computed.
        destruct newer_computed as [newer_q1 newer_q2 newer_q3].
        rewrite newer_q3.
        apply protocol_frontier_below.
    + exact (contributor_covers newer newer_event newer_member).
Qed.

Lemma stored_certificate_locks_agree : forall system authority honest state,
  has_quorum authority honest = true ->
  SafetyConsistent system authority honest state ->
  forall left right,
    In left (safety_certificates state) ->
    In right (safety_certificates state) ->
    ChainCompatible (protocol_lock left) (protocol_lock right).
Proof.
  intros system authority honest state honest_quorum consistent.
  assert (agreement_up_to : forall bound left right,
      In left (safety_certificates state) ->
      In right (safety_certificates state) ->
      length (protocol_root left) + length (protocol_root right) <= bound ->
      ChainCompatible (protocol_lock left) (protocol_lock right)).
  { intro bound. induction bound using lt_wf_ind.
    intros left right left_accepted right_accepted root_bound.
    destruct consistent as
      [computed event_authorities history certificates certificate_authorities
       q3_covered authorities].
    pose proof (certificates left left_accepted) as left_valid.
    pose proof (certificates right right_accepted) as right_valid.
    destruct left_valid as [left_stored left_safe left_quorum].
    destruct right_valid as [right_stored right_safe right_quorum].
    destruct (reduced_quorums_share_honest authority honest
      (protocol_offenders left) (protocol_offenders right)
      (certificate_signers left) (certificate_signers right)
      left_safe right_safe honest_quorum left_quorum right_quorum)
      as [signer [signer_honest [signer_left signer_right]]].
    unfold certificate_signers in signer_left, signer_right.
    apply in_map_iff in signer_left. apply in_map_iff in signer_right.
    destruct signer_left as [left_event [left_signer left_event_member]].
    destruct signer_right as [right_event [right_signer right_event_member]].
    assert (left_honest : In (signed_signer left_event) honest).
    { rewrite left_signer. exact signer_honest. }
    assert (same_signer : signed_signer left_event = signed_signer right_event).
    { rewrite left_signer, right_signer. reflexivity. }
    destruct (Nat.le_ge_cases (signed_time left_event) (signed_time right_event))
      as [left_first | right_first].
    - eapply ordered_certificate_locks_agree with (system := system)
        (older_event := left_event) (newer_event := right_event).
      + refine {| consistent_targets_computed := computed;
          consistent_event_authorities := event_authorities;
          consistent_signing_history := history;
          consistent_certificates := certificates;
          consistent_certificate_authorities := certificate_authorities;
          consistent_q3_covered := q3_covered;
          consistent_authority_transitions := authorities |}.
      + exact left_accepted.
      + exact right_accepted.
      + exact left_event_member.
      + exact right_event_member.
      + exact (history left_event (left_stored left_event left_event_member)
          right_event (right_stored right_event right_event_member)
          left_honest same_signer left_first).
      + exact root_bound.
      + intros pivot pivot_accepted smaller.
        exact (H _ smaller left pivot left_accepted pivot_accepted
          (Nat.le_refl _)).
    - apply chain_compatible_sym.
      assert (right_honest : In (signed_signer right_event) honest).
      { rewrite <- same_signer. exact left_honest. }
      eapply ordered_certificate_locks_agree with (system := system)
        (older_event := right_event) (newer_event := left_event).
      + refine {| consistent_targets_computed := computed;
          consistent_event_authorities := event_authorities;
          consistent_signing_history := history;
          consistent_certificates := certificates;
          consistent_certificate_authorities := certificate_authorities;
          consistent_q3_covered := q3_covered;
          consistent_authority_transitions := authorities |}.
      + exact right_accepted.
      + exact left_accepted.
      + exact right_event_member.
      + exact left_event_member.
      + exact (history right_event (right_stored right_event right_event_member)
          left_event (left_stored left_event left_event_member)
          right_honest (eq_sym same_signer) right_first).
      + rewrite Nat.add_comm. exact root_bound.
      + intros pivot pivot_accepted smaller.
        exact (H _ smaller right pivot right_accepted pivot_accepted
          (Nat.le_refl _)). }
  intros left right left_accepted right_accepted.
  exact (agreement_up_to
    (length (protocol_root left) + length (protocol_root right))
    left right left_accepted right_accepted (Nat.le_refl _)).
Qed.

Lemma stored_certificates_agree : forall system authority honest state,
  has_quorum authority honest = true ->
  SafetyConsistent system authority honest state ->
  forall left right,
    In left (safety_certificates state) ->
    In right (safety_certificates state) ->
    ChainCompatible (protocol_finalized left) (protocol_finalized right).
Proof.
  intros system authority honest state honest_quorum consistent left right
    left_accepted right_accepted.
  apply covered_certificates_agree.
  exact (stored_certificate_locks_agree system authority honest state
    honest_quorum consistent left right left_accepted right_accepted).
Qed.

Theorem protocol_projected_execution_finalized_agreement :
  forall system authority honest state,
    has_quorum authority honest = true ->
    ProjectedExecution system authority honest state ->
    forall left right,
      SafetyFinalized state left ->
      SafetyFinalized state right ->
      ChainCompatible left right.
Proof.
  intros system authority honest state honest_quorum execution left right
    left_finalized right_finalized.
  pose proof (strong_reachable_consistent system authority honest state
    (projected_execution_reachable system authority honest state execution))
    as consistent.
  destruct left_finalized as [left_genesis | left_certificate];
    destruct right_finalized as [right_genesis | right_certificate].
  - subst left. subst right. left. apply chain_reaches_refl.
  - subst left. left. exists right. reflexivity.
  - subst right. right. exists left. reflexivity.
  - destruct left_certificate as [left_stored [left_member left_equal]].
    destruct right_certificate as [right_stored [right_member right_equal]].
    rewrite <- left_equal, <- right_equal.
    exact (stored_certificates_agree system authority honest state honest_quorum
      consistent left_stored right_stored left_member right_member).
Qed.

