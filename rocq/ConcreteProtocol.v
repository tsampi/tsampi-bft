From Coq Require Import List Arith Bool Lia.
From BFT Require Import Protocol.
Import ListNotations.

(** * Canonical chain ancestry *)

Definition chain_reaches (ancestor descendant : Chain) : Prop :=
  exists suffix, descendant = ancestor ++ suffix.

Definition ChainCompatible (left right : Chain) : Prop :=
  chain_reaches left right \/ chain_reaches right left.

Definition block_eq_dec : forall left right : Block, {left = right} + {left <> right}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition chain_eq_dec : forall left right : Chain, {left = right} + {left <> right} :=
  list_eq_dec block_eq_dec.

Lemma chain_reaches_refl : forall chain, chain_reaches chain chain.
Proof. intro chain. exists []. now rewrite app_nil_r. Qed.

Lemma chain_reaches_trans : forall first second third,
  chain_reaches first second -> chain_reaches second third ->
  chain_reaches first third.
Proof.
  intros first second third [middle ->] [last ->].
  exists (middle ++ last). now rewrite app_assoc.
Qed.

Lemma chain_reaches_length : forall ancestor descendant,
  chain_reaches ancestor descendant -> length ancestor <= length descendant.
Proof.
  intros ancestor descendant [suffix ->]. rewrite app_length. lia.
Qed.

Lemma chain_reaches_same_length : forall ancestor descendant,
  chain_reaches ancestor descendant ->
  length ancestor = length descendant -> ancestor = descendant.
Proof.
  intros ancestor descendant [suffix ->] same.
  rewrite app_length in same.
  assert (length suffix = 0) by lia.
  apply length_zero_iff_nil in H. subst suffix. now rewrite app_nil_r.
Qed.

Lemma chain_ancestors_comparable : forall left right tip,
  chain_reaches left tip -> chain_reaches right tip ->
  ChainCompatible left right.
Proof.
  intros left right tip [left_suffix left_eq] [right_suffix right_eq].
  rewrite left_eq in right_eq.
  destruct (app_eq_app left left_suffix right right_suffix right_eq)
    as [suffix [[-> _] | [-> _]]].
  - right. exists suffix. reflexivity.
  - left. exists suffix. reflexivity.
Qed.

Lemma contains_true_iff : forall identity identities,
  contains identity identities = true <-> In identity identities.
Proof.
  intros identity identities. induction identities as [|head rest IH].
  - simpl. split; intro impossible; inversion impossible.
  - simpl. rewrite Bool.orb_true_iff, Nat.eqb_eq, IH.
    intuition congruence.
Qed.

(** * Native scan projection *)

Record ConcreteProtocol := mkConcreteProtocol {
  protocol_block_authority : Block -> Authority;
  protocol_block_parent_signers : Block -> list nat
}.

(** The authority immediately preceding a new Block is the protocol root for
    the first Block and the authority stored by the actual preceding Block
    thereafter. *)
Definition chain_authority
    (system : ConcreteProtocol) (root : Authority) (chain : Chain) : Authority :=
  match rev chain with
  | [] => root
  | block :: _ => protocol_block_authority system block
  end.

Record CarrierAuthorityTransition := mkCarrierAuthorityTransition {
  transition_parent : Authority;
  transition_child : Authority;
  transition_signers : list nat;
  transition_parent_offenders : list nat;
  transition_child_offenders : list nat;
  transition_child_from_evidence :
    transition_child = after_evidence transition_parent transition_child_offenders;
  transition_admitted_by_parent :
    has_quorum transition_parent transition_signers = true
}.

Record AuthorityTransitionValidFrom
    (root : Authority) (honest : list nat)
    (transition : CarrierAuthorityTransition) : Prop := {
  transition_parent_from_root : transition_parent transition =
    after_evidence root (transition_parent_offenders transition);
  transition_parent_evidence_safe : forall offender,
    In offender (transition_parent_offenders transition) -> ~ In offender honest;
  transition_child_evidence_safe : forall offender,
    In offender (transition_child_offenders transition) -> ~ In offender honest
}.

(** One carrier step joins a logged authority transition to the exact chain
    edge it justifies. Matching only the child authority is insufficient: the
    parent and carried signers must be those projected from this edge. *)
Record ConcreteCarrierStep
    (system : ConcreteProtocol) (root : Authority) (prefix : Chain)
    (block : Block) (transition : CarrierAuthorityTransition) : Prop := {
  carrier_transition_parent :
    transition_parent transition = chain_authority system root prefix;
  carrier_transition_child :
    transition_child transition = protocol_block_authority system block;
  carrier_transition_signers :
    transition_signers transition = protocol_block_parent_signers system block
}.

Definition ConcreteCarrierInChain
    (system : ConcreteProtocol) (root : Authority) (chain : Chain)
    (transition : CarrierAuthorityTransition) : Prop :=
  exists prefix block suffix,
    chain = prefix ++ block :: suffix /\
    ConcreteCarrierStep system root prefix block transition.

Inductive ConcreteCarrierTrace
    (system : ConcreteProtocol) (root : Authority)
    (transitions : list CarrierAuthorityTransition) : Chain -> Prop :=
| carrier_trace_genesis : ConcreteCarrierTrace system root transitions []
| carrier_trace_append : forall prefix block transition,
    ConcreteCarrierTrace system root transitions prefix ->
    In transition transitions ->
    ConcreteCarrierStep system root prefix block transition ->
    ConcreteCarrierTrace system root transitions (prefix ++ [block]).

Lemma concrete_carrier_trace_mono :
  forall system root older newer chain,
    ConcreteCarrierTrace system root older chain ->
    (forall transition, In transition older -> In transition newer) ->
    ConcreteCarrierTrace system root newer chain.
Proof.
  intros system root older newer chain trace subset.
  induction trace as [|prefix block transition earlier stored carrier IH].
  - apply carrier_trace_genesis.
  - apply carrier_trace_append with (transition := transition); auto.
Qed.

Lemma concrete_carrier_trace_last :
  forall system root transitions prefix block,
    ConcreteCarrierTrace system root transitions (prefix ++ [block]) ->
    exists transition,
      In transition transitions /\
      ConcreteCarrierStep system root prefix block transition.
Proof.
  intros system root transitions prefix final_block.
  remember (prefix ++ [final_block]) as target eqn:target_edge.
  intro trace. revert prefix final_block target_edge.
  induction trace as
      [|earlier block transition previous stored carrier IH];
      intros prefix final_block target_edge.
  - apply app_cons_not_nil in target_edge. contradiction.
  - apply app_inj_tail in target_edge.
    destruct target_edge as [same_prefix same_block].
    subst prefix. subst final_block. exists transition. auto.
Qed.

Lemma concrete_carrier_step_fields :
  forall system root prefix block transition,
    ConcreteCarrierStep system root prefix block transition ->
    transition_parent transition = chain_authority system root prefix /\
    transition_child transition = protocol_block_authority system block /\
    transition_signers transition = protocol_block_parent_signers system block.
Proof.
  intros system root prefix block transition carrier.
  destruct carrier. auto.
Qed.

Definition protocol_layer (system : ConcreteProtocol) (block : Block) : Layer :=
  mkLayer (block_id block) (protocol_block_authority system block)
    (protocol_block_parent_signers system block).

Definition protocol_genesis_layer : Layer := mkLayer 0 [] [].

Definition protocol_layers (system : ConcreteProtocol) (chain : Chain) : list Layer :=
  map (protocol_layer system) (rev chain) ++ [protocol_genesis_layer].

(** The scan always retains the final Genesis layer. Its remaining length is
    the corresponding oldest-first chain prefix. *)
Definition protocol_frontier (system : ConcreteProtocol) (target : Chain) : Chain :=
  firstn (Nat.pred (length (q1 (protocol_layers system target)))) target.

Definition signer_subset (left right : list nat) : Prop :=
  forall signer, In signer left -> In signer right.

Lemma support_weight_mono : forall authority left right,
  signer_subset left right ->
  support_weight authority left <= support_weight authority right.
Proof.
  intros authority left right subset.
  induction authority as [|[identity weight] rest IH].
  - reflexivity.
  - simpl. destruct (contains identity left) eqn:left_member.
    + assert (right_member : contains identity right = true).
      { apply contains_true_iff. apply subset. now apply contains_true_iff. }
      rewrite right_member. lia.
    + destruct (contains identity right); simpl; lia.
Qed.

Lemma has_quorum_mono : forall authority left right,
  signer_subset left right ->
  has_quorum authority left = true -> has_quorum authority right = true.
Proof.
  intros authority left right subset quorum.
  unfold has_quorum in *. apply Nat.ltb_lt in quorum. apply Nat.ltb_lt.
  pose proof (support_weight_mono authority left right subset). lia.
Qed.

Lemma scan_length_le : forall layers seen,
  length (scan layers seen) <= length layers.
Proof.
  intros layers. induction layers as [|carrier tail IH]; intro seen.
  - reflexivity.
  - destruct tail as [|parent rest].
    + reflexivity.
    + simpl. destruct (has_quorum (layer_authority parent)
        (seen ++ layer_parent_signers carrier)); simpl.
      * lia.
      * specialize (IH (seen ++ layer_parent_signers carrier)). simpl in IH. lia.
Qed.

Lemma scan_seen_monotone : forall layers left_seen right_seen,
  signer_subset left_seen right_seen ->
  length (scan layers left_seen) <= length (scan layers right_seen).
Proof.
  intros layers. induction layers as [|carrier tail IH];
      intros left_seen right_seen subset.
  - reflexivity.
  - destruct tail as [|parent rest].
    + reflexivity.
    + simpl.
      assert (combined_subset : signer_subset
          (left_seen ++ layer_parent_signers carrier)
          (right_seen ++ layer_parent_signers carrier)).
      { intros signer member. apply in_app_iff in member.
        apply in_app_iff. destruct member as [old | carried].
        - left. now apply subset.
        - right. exact carried. }
      destruct (has_quorum (layer_authority parent)
        (left_seen ++ layer_parent_signers carrier)) eqn:left_quorum.
      * pose proof (has_quorum_mono (layer_authority parent)
          (left_seen ++ layer_parent_signers carrier)
          (right_seen ++ layer_parent_signers carrier)
          combined_subset left_quorum) as right_quorum.
        rewrite right_quorum. reflexivity.
      * destruct (has_quorum (layer_authority parent)
          (right_seen ++ layer_parent_signers carrier)) eqn:right_quorum.
        -- change (length (scan (parent :: rest)
              (left_seen ++ layer_parent_signers carrier)) <=
              length (parent :: rest)).
           apply scan_length_le.
        -- change (length (scan (parent :: rest)
              (left_seen ++ layer_parent_signers carrier)) <=
              length (scan (parent :: rest)
                (right_seen ++ layer_parent_signers carrier))).
           apply IH. exact combined_subset.
Qed.

Lemma scan_prefix_length : forall prefix layers seen,
  length (scan layers []) <= length (scan (prefix ++ layers) seen).
Proof.
  induction prefix as [|carrier prefix IH]; intros layers seen.
  - simpl. apply scan_seen_monotone. intros signer impossible. contradiction.
  - simpl app. destruct (prefix ++ layers) as [|parent rest] eqn:joined.
    + apply app_eq_nil in joined. destruct joined as [_ layers_empty].
      subst layers. simpl. lia.
    + simpl. destruct (has_quorum (layer_authority parent)
        (seen ++ layer_parent_signers carrier)) eqn:quorum.
      * pose proof (scan_length_le layers []) as bounded.
        assert (layers_bounded : length layers <= length (parent :: rest)).
        { rewrite <- joined, app_length. lia. }
        exact (Nat.le_trans _ _ _ bounded layers_bounded).
      * specialize (IH layers (seen ++ layer_parent_signers carrier)).
        now rewrite joined in IH.
Qed.

Lemma protocol_layers_app : forall system older suffix,
  protocol_layers system (older ++ suffix) =
    map (protocol_layer system) (rev suffix) ++ protocol_layers system older.
Proof.
  intros. unfold protocol_layers. rewrite rev_app_distr, map_app, app_assoc.
  reflexivity.
Qed.

Lemma protocol_frontier_below : forall system target,
  chain_reaches (protocol_frontier system target) target.
Proof.
  intros system target. unfold protocol_frontier, chain_reaches.
  exists (skipn (Nat.pred (length (q1 (protocol_layers system target)))) target).
  symmetry. apply firstn_skipn.
Qed.

Lemma firstn_reaches_firstn : forall older suffix shorter longer,
  shorter <= length older -> shorter <= longer ->
  chain_reaches (firstn shorter older) (firstn longer (older ++ suffix)).
Proof.
  intros older suffix shorter longer shorter_old shorter_long.
  exists (skipn shorter (firstn longer (older ++ suffix))).
  assert (same_prefix :
      firstn shorter (firstn longer (older ++ suffix)) = firstn shorter older).
  { rewrite firstn_firstn, Nat.min_l by exact shorter_long.
    rewrite firstn_app.
    assert (shorter - length older = 0) by lia.
    rewrite H. simpl. now rewrite app_nil_r. }
  rewrite <- same_prefix. symmetry. apply firstn_skipn.
Qed.

Lemma protocol_frontier_monotone : forall system older newer,
  chain_reaches older newer ->
  chain_reaches (protocol_frontier system older)
    (protocol_frontier system newer).
Proof.
  intros system older newer [suffix ->].
  unfold protocol_frontier.
  set (older_layers := protocol_layers system older).
  set (extra_layers := map (protocol_layer system) (rev suffix)).
  assert (frontier_lengths :
      length (q1 older_layers) <= length (q1 (extra_layers ++ older_layers))).
  { unfold q1. apply scan_prefix_length. }
  assert (projected_lengths :
      Nat.pred (length (q1 older_layers)) <=
      Nat.pred (length (q1 (extra_layers ++ older_layers)))).
  { now apply Nat.pred_le_mono. }
  assert (older_bound_raw : length (q1 older_layers) <= S (length older)).
  { eapply Nat.le_trans. apply scan_length_le.
    subst older_layers. unfold protocol_layers.
    rewrite app_length, map_length, rev_length. simpl. lia. }
  assert (older_bound : Nat.pred (length (q1 older_layers)) <= length older).
  { pose proof (Nat.pred_le_mono _ _ older_bound_raw) as bounded.
    simpl in bounded. exact bounded. }
  rewrite protocol_layers_app. fold older_layers extra_layers.
  now apply firstn_reaches_firstn.
Qed.

