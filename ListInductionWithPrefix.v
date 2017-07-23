Require Import List.
Import ListNotations.

Lemma list_ind'' :
  forall (A : Type) (P : list A -> Prop) (l : list A),
    P nil ->
    (forall a l' prefix, prefix ++ a :: l' = l -> P l' -> P (a :: l')) ->
    forall l' prefix, prefix ++ l' = l -> P l'.
Proof.
  intros A P l Hnil Hcons.
  induction l'; intros prefix E.
  - auto.
  - eapply Hcons. eauto.
    apply IHl' with (prefix := prefix ++ [a]).
    rewrite app_ass.
    auto.
Qed.

Lemma list_ind' :
  forall (A : Type) (P : list A -> Prop) (l : list A),
    P nil ->
    (forall a l' prefix, prefix ++ a :: l' = l -> P l' -> P (a :: l')) ->
    P l.
Proof.
  intros.
  apply list_ind'' with (l := l) (prefix := []); auto.
Qed.
