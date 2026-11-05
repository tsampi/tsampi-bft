From Coq Require Import List Arith Bool Lia.
From BFT Require Import Protocol ConcreteProtocol.
Import ListNotations.

Theorem strict_quorum_intersection :
  forall total left_support right_support overlap,
    2 * total < 3 * left_support ->
    2 * total < 3 * right_support ->
    left_support + right_support <= total + overlap ->
    0 < overlap.
Proof.
  intros. lia.
Qed.

Theorem reduced_authority_intersection :
  forall common_total left_total right_total left_support right_support overlap,
    2 * left_total < 3 * left_support ->
    2 * right_total < 3 * right_support ->
    3 * common_total <= 2 * (left_total + right_total) ->
    left_support + right_support <= common_total + overlap ->
    0 < overlap.
Proof.
  intros. lia.
Qed.

(** * Constructive overlap for evidence-reduced authorities *)

(** A generalized weight fold keeps the quorum arithmetic visibly tied to the
    executable [Authority] representation. *)
Fixpoint selected_weight
    (authority : Authority) (selected : nat -> bool) : nat :=
  match authority with
  | [] => 0
  | (identity, weight) :: rest =>
      (if selected identity then weight else 0) +
      selected_weight rest selected
  end.

Definition retained_after (offenders : list nat) (identity : nat) : bool :=
  negb (contains identity offenders).

Lemma support_weight_selected : forall authority signers,
  support_weight authority signers =
    selected_weight authority (fun identity => contains identity signers).
Proof.
  intros authority signers. induction authority as [|[identity weight] rest IH].
  - reflexivity.
  - simpl. now rewrite IH.
Qed.

Lemma authority_total_selected : forall authority,
  authority_total authority = selected_weight authority (fun _ => true).
Proof.
  intro authority. induction authority as [|[identity weight] rest IH].
  - reflexivity.
  - simpl. now rewrite IH.
Qed.

Lemma after_evidence_selected : forall authority offenders selected,
  selected_weight (after_evidence authority offenders) selected =
  selected_weight authority (fun identity =>
    retained_after offenders identity && selected identity).
Proof.
  intros authority offenders selected.
  induction authority as [|[identity weight] rest IH].
  - reflexivity.
  - simpl. unfold retained_after. destruct (contains identity offenders); simpl;
      now rewrite IH.
Qed.

Lemma selected_weight_le_total : forall authority selected,
  selected_weight authority selected <= authority_total authority.
Proof.
  intros authority selected. induction authority as [|[identity weight] rest IH].
  - simpl. lia.
  - simpl. destruct (selected identity); simpl; lia.
Qed.

Lemma selected_weight_ext : forall authority left right,
  (forall identity, left identity = right identity) ->
  selected_weight authority left = selected_weight authority right.
Proof.
  intros authority left right same.
  induction authority as [|[identity weight] rest IH].
  - reflexivity.
  - simpl. rewrite (same identity), IH. reflexivity.
Qed.

Lemma selected_weight_positive_member : forall authority selected,
  0 < selected_weight authority selected ->
  exists identity weight,
    In (identity, weight) authority /\ selected identity = true /\ 0 < weight.
Proof.
  intros authority selected positive.
  induction authority as [|[identity weight] rest IH].
  - simpl in positive. lia.
  - simpl in positive. destruct (selected identity) eqn:selected_here.
    + destruct (Nat.eq_dec weight 0) as [zero | nonzero].
      * subst weight. simpl in positive.
        destruct (IH positive) as [found [found_weight evidence]].
        exists found, found_weight. intuition.
      * exists identity, weight. simpl. intuition lia.
    + simpl in positive.
      destruct (IH positive) as [found [found_weight evidence]].
      exists found, found_weight. intuition.
Qed.

Lemma selected_weight_cover : forall authority universe selected honest,
  (forall identity, selected identity = true -> universe identity = true) ->
  (forall identity, honest identity = true -> universe identity = true) ->
  selected_weight authority selected + selected_weight authority honest <=
  selected_weight authority universe +
    selected_weight authority (fun identity => selected identity && honest identity).
Proof.
  intros authority universe selected honest selected_in honest_in.
  induction authority as [|[identity weight] rest IH].
  - simpl. lia.
  - simpl.
    destruct (selected identity) eqn:selected_here;
      destruct (honest identity) eqn:honest_here;
      simpl in *;
      try rewrite (selected_in identity selected_here);
      try rewrite (honest_in identity honest_here); simpl; lia.
Qed.

Lemma honest_is_retained : forall offenders honest,
  (forall offender, In offender offenders -> ~ In offender honest) ->
  forall identity, contains identity honest = true ->
    retained_after offenders identity = true.
Proof.
  intros offenders honest safe identity in_honest.
  unfold retained_after.
  destruct (contains identity offenders) eqn:in_offenders; simpl; auto.
  exfalso. apply (safe identity).
  - now apply contains_true_iff.
  - now apply contains_true_iff.
Qed.

Lemma three_quorums_have_honest_overlap :
  forall left_support right_support honest_support
      left_total right_total root_total left_honest right_honest triple,
    2 * left_total < 3 * left_support ->
    2 * right_total < 3 * right_support ->
    2 * root_total < 3 * honest_support ->
    left_support + honest_support <= left_total + left_honest ->
    right_support + honest_support <= right_total + right_honest ->
    left_honest + right_honest <= honest_support + triple ->
    left_total <= root_total -> right_total <= root_total -> 0 < triple.
Proof. intros. lia. Qed.

Lemma reduced_quorums_share_honest :
  forall authority honest left_offenders right_offenders left right,
    (forall offender, In offender left_offenders -> ~ In offender honest) ->
    (forall offender, In offender right_offenders -> ~ In offender honest) ->
    has_quorum authority honest = true ->
    has_quorum (after_evidence authority left_offenders) left = true ->
    has_quorum (after_evidence authority right_offenders) right = true ->
    exists signer, In signer honest /\ In signer left /\ In signer right.
Proof.
  intros authority honest left_offenders right_offenders left right
    left_safe right_safe honest_quorum left_quorum right_quorum.
  set (honest_set := fun identity => contains identity honest).
  set (left_retained := retained_after left_offenders).
  set (right_retained := retained_after right_offenders).
  set (left_set := fun identity =>
    left_retained identity && contains identity left).
  set (right_set := fun identity =>
    right_retained identity && contains identity right).
  assert (left_honest_retained : forall identity,
      honest_set identity = true -> left_retained identity = true).
  { intros identity member. apply honest_is_retained with (honest := honest);
      assumption. }
  assert (right_honest_retained : forall identity,
      honest_set identity = true -> right_retained identity = true).
  { intros identity member. apply honest_is_retained with (honest := honest);
      assumption. }
  assert (left_set_retained : forall identity,
      left_set identity = true -> left_retained identity = true).
  { intros identity member. apply andb_true_iff in member.
    destruct member as [retained _]. exact retained. }
  assert (right_set_retained : forall identity,
      right_set identity = true -> right_retained identity = true).
  { intros identity member. apply andb_true_iff in member.
    destruct member as [retained _]. exact retained. }
  pose proof (selected_weight_cover authority left_retained left_set
    honest_set left_set_retained left_honest_retained) as left_cover.
  pose proof (selected_weight_cover authority right_retained right_set
    honest_set right_set_retained right_honest_retained) as right_cover.
  pose proof (selected_weight_le_total authority left_retained) as left_total_le.
  pose proof (selected_weight_le_total authority right_retained) as right_total_le.
  unfold has_quorum in honest_quorum, left_quorum, right_quorum.
  apply Nat.ltb_lt in honest_quorum.
  apply Nat.ltb_lt in left_quorum.
  apply Nat.ltb_lt in right_quorum.
  rewrite support_weight_selected in honest_quorum.
  rewrite support_weight_selected in left_quorum.
  rewrite support_weight_selected in right_quorum.
  rewrite authority_total_selected in honest_quorum.
  rewrite authority_total_selected in left_quorum.
  rewrite authority_total_selected in right_quorum.
  repeat rewrite after_evidence_selected in left_quorum.
  repeat rewrite after_evidence_selected in right_quorum.
  change (2 * selected_weight authority (fun _ => true) <
      3 * selected_weight authority honest_set) in honest_quorum.
  change (2 * selected_weight authority
      (fun identity => left_retained identity && true) <
      3 * selected_weight authority left_set) in left_quorum.
  change (2 * selected_weight authority
      (fun identity => right_retained identity && true) <
      3 * selected_weight authority right_set) in right_quorum.
  assert (left_total_normal :
      selected_weight authority (fun identity => left_retained identity && true) =
      selected_weight authority left_retained).
  { apply selected_weight_ext. intro identity.
    now destruct (left_retained identity). }
  assert (right_total_normal :
      selected_weight authority (fun identity => right_retained identity && true) =
      selected_weight authority right_retained).
  { apply selected_weight_ext. intro identity.
    now destruct (right_retained identity). }
  rewrite left_total_normal in left_quorum.
  rewrite right_total_normal in right_quorum.
  change (selected_weight authority left_set +
      selected_weight authority honest_set <=
      selected_weight authority left_retained +
      selected_weight authority (fun identity =>
        left_set identity && honest_set identity)) in left_cover.
  change (selected_weight authority right_set +
      selected_weight authority honest_set <=
      selected_weight authority right_retained +
      selected_weight authority (fun identity =>
        right_set identity && honest_set identity)) in right_cover.
  (* The three-way count is the exact arithmetic fact needed here. Pairwise
     intersection lemmas are useful compatibility results, but neither one
     entails an honest member shared by both reduced certificates. *)
  pose proof (selected_weight_cover authority honest_set
    (fun identity => left_set identity && honest_set identity)
    (fun identity => right_set identity && honest_set identity))
    as honest_intersection_cover.
  assert (left_honest_in : forall identity,
      left_set identity && honest_set identity = true ->
      honest_set identity = true).
  { intros identity member. apply andb_true_iff in member. intuition. }
  assert (right_honest_in : forall identity,
      right_set identity && honest_set identity = true ->
      honest_set identity = true).
  { intros identity member. apply andb_true_iff in member. intuition. }
  specialize (honest_intersection_cover left_honest_in right_honest_in).
  rewrite authority_total_selected in left_total_le, right_total_le.
  assert (triple_positive : 0 < selected_weight authority (fun identity =>
      (left_set identity && honest_set identity) &&
      (right_set identity && honest_set identity))).
  { exact (three_quorums_have_honest_overlap
      (selected_weight authority left_set)
      (selected_weight authority right_set)
      (selected_weight authority honest_set)
      (selected_weight authority left_retained)
      (selected_weight authority right_retained)
      (selected_weight authority (fun _ => true))
      (selected_weight authority (fun identity =>
        left_set identity && honest_set identity))
      (selected_weight authority (fun identity =>
        right_set identity && honest_set identity))
      (selected_weight authority (fun identity =>
        (left_set identity && honest_set identity) &&
        (right_set identity && honest_set identity)))
      left_quorum right_quorum honest_quorum left_cover right_cover
      honest_intersection_cover left_total_le right_total_le). }
  destruct (selected_weight_positive_member authority
    (fun identity =>
      (left_set identity && honest_set identity) &&
      (right_set identity && honest_set identity)) triple_positive)
    as [signer [weight [stored [selected weight_positive]]]].
  apply andb_true_iff in selected. destruct selected as [left_honest right_honest].
  apply andb_true_iff in left_honest. destruct left_honest as [in_left is_honest].
  apply andb_true_iff in right_honest. destruct right_honest as [in_right _].
  apply andb_true_iff in in_left. destruct in_left as [_ in_left].
  apply andb_true_iff in in_right. destruct in_right as [_ in_right].
  exists signer. split.
  - apply contains_true_iff. exact is_honest.
  - split; apply contains_true_iff; assumption.
Qed.
