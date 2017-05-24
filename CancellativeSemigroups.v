Definition inj{X Y}(f : X -> Y) := forall x x', f x = f x' -> x = x'.

Definition surj{X Y}(f : X -> Y) := forall y, {x : X & f x = y}.

Definition ded_fin(X : Set) := forall f : X -> X, inj f -> surj f.

Section df_inh_cancel_sgroups.

Variable X : Set.
Variable x0 : X.
Variable m : X -> X -> X.

Infix "*" := m.

Hypothesis X_df : ded_fin X.
Hypothesis assoc : forall x y z, x * (y * z) = (x * y) * z.
Hypothesis l_cancel : forall x y z, x * y = x * z -> y = z.
Hypothesis r_cancel : forall x y z, y * x = z * x -> y = z.

Definition act_left (x : X) : X -> X := fun y => x * y.

Lemma act_left_inj : forall x, inj (act_left x).
Proof. unfold act_left, inj. eauto. Qed.

(* the identity *)
Definition e : X :=
  projT1 (X_df (act_left x0) (act_left_inj _) x0).

Theorem l_id : forall x, e * x = x.
Proof.
  unfold e.
  intros x.
  destruct (X_df (act_left x0) (act_left_inj x0) x0) as [e H].
  simpl.
  unfold act_left in *.
  apply l_cancel with (x := x0).
  rewrite assoc.
  now rewrite H.
Qed.

Theorem r_id : forall x, x * e = x.
Proof.
  intros x.
  apply r_cancel with (x := e).
  rewrite <- assoc.
  now rewrite l_id.
Qed.

Definition act_right (x : X) : X -> X := fun y => y * x.

Lemma act_right_inj : forall x, inj (act_right x).
Proof. unfold act_right, inj. eauto. Qed.

(* the inverse operation *)
Definition inv : X -> X := fun x =>
  projT1 (X_df (act_right x) (act_right_inj _) e).

Theorem l_inv : forall x, (inv x) * x = e.
Proof.
  intros x.
  unfold inv.
  destruct (X_df (act_right x) (act_right_inj _) _) as [x' H].
  simpl.
  unfold act_right in *.
  auto.
Qed.

Theorem r_inv : forall x, x * (inv x) = e.
Proof.
  intros x.
  apply l_cancel with (x := inv x).
  rewrite assoc.
  now rewrite l_inv, l_id, r_id.
Qed.

End df_inh_cancel_sgroups.