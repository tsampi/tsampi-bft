From Coq Require Import List Arith Bool.
Import ListNotations.

Record Block := mkBlock {
  block_id : nat;
  block_signer : nat;
  block_position : nat;
  block_score : nat
}.

Definition Chain := list Block.
Definition Authority := list (nat * nat).

Fixpoint contains (wanted : nat) (values : list nat) : bool :=
  match values with
  | [] => false
  | value :: rest => Nat.eqb wanted value || contains wanted rest
  end.

Fixpoint authority_weight (authority : Authority) (wanted : nat) : nat :=
  match authority with
  | [] => 0
  | (identity, weight) :: rest =>
      if Nat.eqb identity wanted then weight else authority_weight rest wanted
  end.

Fixpoint authority_total (authority : Authority) : nat :=
  match authority with
  | [] => 0
  | (_, weight) :: rest => weight + authority_total rest
  end.

Fixpoint support_weight (authority : Authority) (signers : list nat) : nat :=
  match authority with
  | [] => 0
  | (identity, weight) :: rest =>
      (if contains identity signers then weight else 0) +
      support_weight rest signers
  end.

Definition has_quorum (authority : Authority) (signers : list nat) : bool :=
  Nat.ltb (2 * authority_total authority) (3 * support_weight authority signers).

Definition after_evidence (authority : Authority) (offenders : list nat) : Authority :=
  filter (fun member => negb (contains (fst member) offenders)) authority.

Definition compare_blocks (left right : Block) : comparison :=
  match Nat.compare (block_score left) (block_score right) with
  | Lt => Gt
  | Gt => Lt
  | Eq => Nat.compare (block_id left) (block_id right)
  end.

Fixpoint compare_chains (left right : Chain) : comparison :=
  match left, right with
  | [], [] => Eq
  | [], _ :: _ => Gt
  | _ :: _, [] => Lt
  | a :: left_rest, b :: right_rest =>
      if Nat.eqb (block_id a) (block_id b)
      then compare_chains left_rest right_rest
      else compare_blocks a b
  end.

Fixpoint list_eqb {A : Type} (equal : A -> A -> bool)
    (left right : list A) : bool :=
  match left, right with
  | [], [] => true
  | a :: left_rest, b :: right_rest =>
      equal a b && list_eqb equal left_rest right_rest
  | _, _ => false
  end.

Definition path_prefix (left right : list nat) : bool :=
  list_eqb Nat.eqb left (firstn (length left) right) &&
  Nat.leb (length left) (length right).

Record Layer := mkLayer {
  layer_target : nat;
  layer_authority : Authority;
  layer_parent_signers : list nat
}.

Fixpoint scan (layers : list Layer) (seen : list nat) : list Layer :=
  match layers with
  | [] => []
  | [base] => [base]
  | carrier :: ((parent :: rest) as parents) =>
      let combined := seen ++ layer_parent_signers carrier in
      if has_quorum (layer_authority parent) combined
      then parents
      else scan parents combined
  end.

Definition q1 (layers : list Layer) : list Layer := scan layers [].
Definition q2 (layers : list Layer) : list Layer := q1 (q1 layers).
Definition q3 (layers : list Layer) : list Layer := q1 (q2 layers).

Definition scanned_target (layers : list Layer) : nat :=
  match layers with
  | [] => 0
  | layer :: _ => layer_target layer
  end.

Definition selected_candidate (inventory : list Chain) : option Chain :=
  match inventory with
  | [] => None
  | first :: _ => Some first
  end.

Definition ranked_against_all (best : Chain) (inventory : list Chain) : bool :=
  forallb (fun candidate =>
    match compare_chains best candidate with Gt => false | _ => true end)
    inventory.

Fixpoint finalized_prefix
    (before after : list (list nat)) : bool :=
  match before, after with
  | [], [] => true
  | old :: olds, new :: news => path_prefix old new && finalized_prefix olds news
  | _, _ => false
  end.

Definition comparable_paths (left right : list nat) : bool :=
  path_prefix left right || path_prefix right left.

Fixpoint comparable_with
    (path : list nat) (paths : list (list nat)) : bool :=
  match paths with
  | [] => true
  | other :: rest => comparable_paths path other && comparable_with path rest
  end.

Fixpoint projected_agreement (paths : list (list nat)) : bool :=
  match paths with
  | [] => true
  | path :: rest => comparable_with path rest && projected_agreement rest
  end.

Definition progressed (paths : list (list nat)) : bool :=
  existsb (fun path => Nat.ltb 1 (length path)) paths.

Record AuthorityCase := mkAuthorityCase {
  authority_parent : Authority;
  authority_child : Authority;
  authority_signers : list nat;
  authority_offenders : list nat
}.

Definition authority_eqb (left right : Authority) : bool :=
  list_eqb (fun a b => Nat.eqb (fst a) (fst b) && Nat.eqb (snd a) (snd b))
    left right.

Definition authority_case_ok (value : AuthorityCase) : bool :=
  has_quorum (authority_parent value) (authority_signers value) &&
  authority_eqb
    (after_evidence (authority_parent value) (authority_offenders value))
    (authority_child value).

Inductive ActionKind :=
| SignVote
| Propose
| PublishVote
| PublishProposal
| DeliverVote
| DeliverProposal
| Idle.

Definition action_limit (kind : ActionKind) : nat :=
  match kind with
  | SignVote => 1
  | Propose => 2
  | _ => 0
  end.

Definition bool_nat (value : bool) : nat := if value then 1 else 0.
Definition comparison_nat (value : comparison) : nat :=
  match value with Lt => 0 | Eq => 1 | Gt => 2 end.
