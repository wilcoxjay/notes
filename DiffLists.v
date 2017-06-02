Require Import Coq.Lists.List.
Require Import FunctionalExtensionality.
Import ListNotations.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.ProofIrrelevanceFacts.

Set Implicit Arguments.

Module dlist.

  Definition t' A := list A -> list A.

  Definition prepender A (f : t' A) : Prop :=
    exists lf, forall l, f l = lf ++ l.

  Definition t A := {f : t' A | prepender f}.

  Definition toList A (d : t A) : list A := proj1_sig d [].

  Definition fromList A (l : list A) : t A.
    refine (exist _ (app l) _).
    red.
    eauto.
  Defined.

  Theorem from_to_id :
    forall (a : Set) (xs : list a),
      toList (fromList xs) = xs.
  Proof.
    unfold toList, fromList.
    simpl.
    intros.
    now rewrite app_nil_r.
  Qed.

  Theorem to_from_id :
    forall (a : Set) (xs : t a),
      fromList (toList xs) = xs.
  Proof.
    destruct xs as [f [l H]].
    unfold fromList, toList.
    simpl.
    apply subset_eq_compat.
    apply functional_extensionality.
    intros x.
    rewrite H.
    rewrite H.
    rewrite app_ass.
    reflexivity.
  Qed.
End dlist.
