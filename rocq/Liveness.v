From Coq Require Import List.
From BFT Require Import Protocol Ranking.
Import ListNotations.

Definition frontier2 (frontier : Chain -> Chain) (target : Chain) : Chain :=
  frontier (frontier target).

Definition frontier3 (frontier : Chain -> Chain) (target : Chain) : Chain :=
  frontier (frontier2 frontier target).

Record QuorumStep
    (reaches : Chain -> Chain -> Prop) (frontier : Chain -> Chain)
    (parent child : Chain) : Prop := mkQuorumStep {
  step_descends : reaches parent child;
  step_new_target : child <> parent;
  step_q1 : frontier child = parent
}.

Record HonestQuorumStep
    (reaches : Chain -> Chain -> Prop) (frontier : Chain -> Chain)
    (honest : list nat) (endorsed : nat -> Chain -> Prop)
    (parent child : Chain) : Prop := mkHonestQuorumStep {
  honest_step : QuorumStep reaches frontier parent child;
  honest_votes_validated : forall signer,
    In signer honest -> endorsed signer parent
}.

Lemma three_quorum_steps_reach_parent :
  forall reaches frontier parent first second third,
    QuorumStep reaches frontier parent first ->
    QuorumStep reaches frontier first second ->
    QuorumStep reaches frontier second third ->
    frontier3 frontier third = parent.
Proof.
  intros reaches frontier parent first second third step1 step2 step3.
  unfold frontier3, frontier2.
  rewrite (step_q1 reaches frontier second third step3).
  rewrite (step_q1 reaches frontier first second step2).
  exact (step_q1 reaches frontier parent first step1).
Qed.

Record HonestProtocolActivity
    (reaches : Chain -> Chain -> Prop) (frontier : Chain -> Chain)
    (honest : list nat) (endorsed : nat -> Chain -> Prop) : Prop :=
  mkHonestProtocolActivity {
    next_honest_quorum : forall parent,
      exists child,
        HonestQuorumStep reaches frontier honest endorsed parent child
  }.

Record EventualDelivery
    (honest : list nat) (observed : nat -> list Chain)
    (inventory : list Chain) : Prop := mkEventualDelivery {
  eventually_delivered : forall validator,
    In validator honest -> observed validator = inventory
}.

Record CanonicalInventory (valid_candidate : Chain -> Prop) :=
  mkCanonicalInventory {
    inventory_candidates : list Chain;
    inventory_selected : Chain;
    selected_at_head :
      selected_candidate inventory_candidates = Some inventory_selected;
    selected_valid : valid_candidate inventory_selected;
    selected_best : forall candidate,
      In candidate inventory_candidates ->
      compare_chains inventory_selected candidate <> Gt
  }.

Theorem ranked_finite_inventory_conditional_four_step_liveness :
  forall reaches frontier honest endorsed valid_candidate
      (inventory : CanonicalInventory valid_candidate) observed,
    EventualDelivery honest observed (inventory_candidates valid_candidate inventory) ->
    HonestProtocolActivity reaches frontier honest endorsed ->
    exists first second third fourth,
      (forall validator,
        In validator honest ->
        selected_candidate (observed validator) =
          Some (inventory_selected valid_candidate inventory)) /\
      valid_candidate (inventory_selected valid_candidate inventory) /\
      (forall candidate,
        In candidate (inventory_candidates valid_candidate inventory) ->
        compare_chains (inventory_selected valid_candidate inventory) candidate <> Gt) /\
      HonestQuorumStep reaches frontier honest endorsed
        (inventory_selected valid_candidate inventory) first /\
      HonestQuorumStep reaches frontier honest endorsed first second /\
      HonestQuorumStep reaches frontier honest endorsed second third /\
      HonestQuorumStep reaches frontier honest endorsed third fourth /\
      frontier3 frontier third = inventory_selected valid_candidate inventory /\
      frontier3 frontier fourth = first /\
      first <> inventory_selected valid_candidate inventory.
Proof.
  intros reaches frontier honest endorsed valid_candidate inventory observed
    delivery activity.
  destruct activity as [advance].
  destruct (advance (inventory_selected valid_candidate inventory))
    as [first step1].
  destruct (advance first) as [second step2].
  destruct (advance second) as [third step3].
  destruct (advance third) as [fourth step4].
  exists first, second, third, fourth.
  refine (conj _ _).
  - intros validator member.
    rewrite (eventually_delivered honest observed
      (inventory_candidates valid_candidate inventory) delivery validator member).
    exact (selected_at_head valid_candidate inventory).
  - refine (conj (selected_valid valid_candidate inventory) _).
    refine (conj (selected_best valid_candidate inventory) _).
    refine (conj step1 _).
    refine (conj step2 _).
    refine (conj step3 _).
    refine (conj step4 _).
    refine (conj _ (conj _ _)).
  + eapply three_quorum_steps_reach_parent.
    * exact (honest_step _ _ _ _ _ _ step1).
    * exact (honest_step _ _ _ _ _ _ step2).
    * exact (honest_step _ _ _ _ _ _ step3).
  + eapply three_quorum_steps_reach_parent.
    * exact (honest_step _ _ _ _ _ _ step2).
    * exact (honest_step _ _ _ _ _ _ step3).
    * exact (honest_step _ _ _ _ _ _ step4).
  + exact (step_new_target reaches frontier
      (inventory_selected valid_candidate inventory) first
      (honest_step _ _ _ _ _ _ step1)).
Qed.
