From Coq Require Import List Arith.
From BFT Require Import CatchupSafety.
Import ListNotations.

Section Reachable.
  Context {A : Type} (ancestor : A -> A -> Prop).
  Context
    (ancestor_refl : forall block, ancestor block block)
    (ancestor_trans : forall first second third,
      ancestor first second -> ancestor second third -> ancestor first third)
    (ancestors_comparable : forall left right tip,
      ancestor left tip -> ancestor right tip -> Compatible ancestor left right).

  Record ProtocolState := mkState {
    accepted_certificates : list (CoveredCertificate ancestor);
    durable_votes : list A;
    authority_updates : nat
  }.

  Definition genesis_state : ProtocolState := mkState [] [] 0.

  Definition CertificateSafe
      (state : ProtocolState) (certificate : CoveredCertificate ancestor) : Prop :=
    forall previous,
      In previous (accepted_certificates state) ->
      exists common,
        ancestor (certificate_lock ancestor previous) common /\
        ancestor (certificate_lock ancestor certificate) common.

  Inductive ProtocolStep : ProtocolState -> ProtocolState -> Prop :=
  | step_stutter : forall state,
      ProtocolStep state state
  | step_admit_certificate : forall before certificate,
      CertificateSafe before certificate ->
      ProtocolStep before
        (mkState
          (accepted_certificates before ++ [certificate])
          (durable_votes before)
          (authority_updates before))
  | step_emit_vote : forall before vote,
      ProtocolStep before
        (mkState
          (accepted_certificates before)
          (durable_votes before ++ [vote])
          (authority_updates before))
  | step_apply_authority : forall before,
      ProtocolStep before
        (mkState
          (accepted_certificates before)
          (durable_votes before)
          (S (authority_updates before))).

  Inductive PythonExecution : ProtocolState -> Prop :=
  | execution_genesis : PythonExecution genesis_state
  | execution_action : forall before after,
      PythonExecution before ->
      ProtocolStep before after ->
      PythonExecution after.

  Definition CertificateAgreement (state : ProtocolState) : Prop :=
    forall left right,
      In left (accepted_certificates state) ->
      In right (accepted_certificates state) ->
      Compatible ancestor
        (certificate_finalized ancestor left)
        (certificate_finalized ancestor right).

  Lemma compatible_sym :
    forall left right,
      Compatible ancestor left right -> Compatible ancestor right left.
  Proof.
    intros left right compatible.
    destruct compatible as [forward | reverse].
    - right. exact forward.
    - left. exact reverse.
  Qed.

  Lemma protocol_step_preserves_certificate_agreement :
    forall before after,
      ProtocolStep before after ->
      CertificateAgreement before ->
      CertificateAgreement after.
  Proof.
    intros before after step agreement.
    destruct step as
        [state | before certificate safe | before vote | before].
    - exact agreement.
    - unfold CertificateAgreement in *. simpl.
      intros left right left_member right_member.
      apply in_app_iff in left_member.
      apply in_app_iff in right_member.
      destruct left_member as [left_old | left_new];
        destruct right_member as [right_old | right_new].
      + exact (agreement left right left_old right_old).
      + destruct right_new as [right_equal | impossible].
        2: contradiction.
        subst right.
        destruct (safe left left_old) as [common [left_common new_common]].
        eapply certificate_covered_catchup_safety;
          eauto using ancestor_trans, ancestors_comparable.
      + destruct left_new as [left_equal | impossible].
        2: contradiction.
        subst left.
        apply compatible_sym.
        destruct (safe right right_old) as [common [right_common new_common]].
        eapply certificate_covered_catchup_safety;
          eauto using ancestor_trans, ancestors_comparable.
      + destruct left_new as [left_equal | impossible].
        2: contradiction.
        destruct right_new as [right_equal | impossible].
        2: contradiction.
        subst left. subst right.
        left. apply ancestor_refl.
    - exact agreement.
    - exact agreement.
  Qed.

  Theorem execution_certificate_agreement :
    forall state,
      PythonExecution state -> CertificateAgreement state.
  Proof.
    intros state execution.
    induction execution as [|before after earlier step IH].
    - unfold CertificateAgreement. simpl. intros. contradiction.
    - eapply protocol_step_preserves_certificate_agreement; eauto.
  Qed.

  Definition Finalized
      (genesis : A) (state : ProtocolState) (block : A) : Prop :=
    block = genesis \/
    exists certificate,
      In certificate (accepted_certificates state) /\
      certificate_finalized ancestor certificate = block.

  Theorem reachable_projected_execution_finalized_agreement :
    forall genesis state,
      (forall block, ancestor genesis block) ->
      PythonExecution state ->
      forall left right,
        Finalized genesis state left ->
        Finalized genesis state right ->
        Compatible ancestor left right.
  Proof.
    intros genesis state genesis_below execution left right left_final right_final.
    destruct left_final as [left_genesis | left_certificate];
      destruct right_final as [right_genesis | right_certificate].
    - subst left. subst right. left. apply ancestor_refl.
    - subst left. destruct right_certificate as [certificate [stored finalized]].
      left. rewrite <- finalized. apply genesis_below.
    - subst right. destruct left_certificate as [certificate [stored finalized]].
      right. rewrite <- finalized. apply genesis_below.
    - destruct left_certificate as [left_certificate [left_stored left_equal]].
      destruct right_certificate as [right_certificate [right_stored right_equal]].
      rewrite <- left_equal, <- right_equal.
      exact (execution_certificate_agreement state execution
        left_certificate right_certificate left_stored right_stored).
  Qed.
End Reachable.
