From BFT Require Import Protocol.

Definition Compatible {A : Type} (ancestor : A -> A -> Prop) (left right : A) : Prop :=
  ancestor left right \/ ancestor right left.

Record CoveredCertificate {A : Type} (ancestor : A -> A -> Prop) := {
  certificate_finalized : A;
  certificate_lock : A;
  certificate_covered : ancestor certificate_finalized certificate_lock
}.

Theorem certificate_covered_catchup_safety :
  forall (A : Type) (ancestor : A -> A -> Prop),
    (forall x y z, ancestor x y -> ancestor y z -> ancestor x z) ->
    (forall x y tip, ancestor x tip -> ancestor y tip ->
      Compatible ancestor x y) ->
    forall (old new : CoveredCertificate ancestor) common,
      ancestor (certificate_lock ancestor old) common ->
      ancestor (certificate_lock ancestor new) common ->
      Compatible ancestor
        (certificate_finalized ancestor old)
        (certificate_finalized ancestor new).
Proof.
  intros A ancestor trans comparable old new common old_common new_common.
  apply (comparable _ _ common).
  - eapply trans; [exact (@certificate_covered A ancestor old) | exact old_common].
  - eapply trans; [exact (@certificate_covered A ancestor new) | exact new_common].
Qed.
