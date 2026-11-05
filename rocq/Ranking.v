From Coq Require Import List Arith Bool.
From BFT Require Import Protocol.
Import ListNotations.

Theorem compare_chains_first_divergence :
  forall left right left_rest right_rest,
    block_id left <> block_id right ->
    compare_chains (left :: left_rest) (right :: right_rest) =
      compare_blocks left right.
Proof.
  intros left right left_rest right_rest distinct.
  simpl. apply Nat.eqb_neq in distinct. rewrite distinct. reflexivity.
Qed.

Lemma compare_chains_self :
  forall chain, compare_chains chain chain = Eq.
Proof.
  induction chain as [|block rest IH].
  - reflexivity.
  - simpl. rewrite Nat.eqb_refl. exact IH.
Qed.

Lemma compare_chains_common_prefix :
  forall prefix left right,
    compare_chains (prefix ++ left) (prefix ++ right) =
      compare_chains left right.
Proof.
  induction prefix as [|block rest IH]; intros left right.
  - reflexivity.
  - simpl. rewrite Nat.eqb_refl. exact (IH left right).
Qed.

Lemma compare_chains_descendant :
  forall prefix suffix,
    suffix <> [] -> compare_chains (prefix ++ suffix) prefix = Lt.
Proof.
  induction prefix as [|block rest IH]; intros suffix nonempty.
  - destruct suffix as [|head tail].
    + contradiction.
    + reflexivity.
  - simpl. rewrite Nat.eqb_refl. apply IH. exact nonempty.
Qed.

Inductive RankedSwitch : Chain -> Chain -> Prop :=
| switch_descendant : forall older suffix,
    suffix <> [] -> RankedSwitch older (older ++ suffix)
| switch_better : forall older newer,
    compare_chains newer older = Lt -> RankedSwitch older newer
| switch_same : forall chain,
    RankedSwitch chain chain.

Theorem ranked_switch_obligation :
  forall older newer,
    RankedSwitch older newer -> compare_chains newer older <> Gt.
Proof.
  intros older newer switch.
  destruct switch as
      [older suffix nonempty | older newer better | chain].
  - rewrite compare_chains_descendant by exact nonempty. discriminate.
  - rewrite better. discriminate.
  - rewrite compare_chains_self. discriminate.
Qed.

Theorem equal_rank_is_permitted :
  forall chain, RankedSwitch chain chain.
Proof.
  exact switch_same.
Qed.
