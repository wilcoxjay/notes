Require Import Omega Bool.

Definition LPO := forall f : nat -> bool, (exists x, f x = true) \/ (forall x, f x = false).

Definition decr(f : nat -> nat) := forall n, f (S n) <= f n.

Lemma decr_trans :
  forall f,
    decr f ->
    forall x y,
      x <= y -> f y <= f x.
Proof.
  intros f Decr.
  induction 1.
  - auto.
  - specialize (Decr m). omega.
Qed.

Definition infvalley (f : nat -> nat) (x : nat) := forall y, x <= y -> f y = f x.

Fixpoint f_down (f : nat -> bool) (n : nat) : bool :=
  match n with
  | 0 => f 0
  | S n => f_down f n || f (S n)
  end.

Lemma f_down_S_true :
  forall f n,
    f_down f n = true ->
    f_down f (S n) = true.
Proof.
  intros.
  simpl.
  apply orb_true_intro.
  auto.
Qed.

Definition f_down_nat (f : nat -> bool) (n : nat) : nat :=
   Nat.b2n (negb (f_down f n)).

Lemma f_down_nat_decr :
  forall f,
    decr (f_down_nat f).
Proof.
  intros f n.
  unfold f_down_nat.
  destruct (f_down f n) eqn:?.
  - now rewrite f_down_S_true by auto.
  - destruct (negb (f_down _ _)); simpl; auto.
Qed.

Lemma f_down_true:
  forall f n,
    f_down f n = true -> exists n' : nat, n' <= n /\ f n' = true.
Proof.
  induction n; simpl.
  - eauto.
  - rewrite orb_true_iff. intuition eauto.
    destruct H as (n' & Lt & F). exists n'. eauto with *.
Qed.

Lemma f_down_nat_0_elim :
  forall f x,
    f_down_nat f x = 0 ->
    exists x', x' <= x /\ f x' = true.
Proof.
  unfold f_down_nat, Nat.b2n.
  intros.
  destruct (negb _) eqn:?; try discriminate.
  rewrite negb_false_iff in *.
  auto using f_down_true.
Qed.

Lemma f_down_false:
  forall f x,
    f_down f x = false ->
    forall y : nat, y <= x -> f y = false.
Proof.
  induction x; simpl; intros F y Lt.
  - assert (y = 0) by omega. congruence.
  - rewrite orb_false_iff in F. destruct F as [FD F].
    assert (y <= x \/ y = S x) by omega.
    intuition.
    congruence.
Qed.

Lemma f_down_nat_S_elim :
  forall f x n,
    f_down_nat f x = S n ->
    forall y, y <= x -> f y = false.
Proof.
  unfold f_down_nat, Nat.b2n.
  intros.
  destruct (negb _) eqn:F; try discriminate.
  rewrite negb_true_iff in F.
  eauto using f_down_false.
Qed.

Lemma f_down_false_intro :
  forall f x,
    (forall y, y <= x -> f y = false) ->
    f_down f x = false.
Proof.
  induction x; simpl; intros.
  - auto.
  - rewrite orb_false_iff. auto.
Qed.

Lemma f_down_nat_S_intro :
  forall f x,
    (forall y, y <= x -> f y = false) ->
    f_down_nat f x = 1.
Proof.
  unfold f_down_nat, Nat.b2n.
  intros.
  rewrite f_down_false_intro; auto.
Qed.

Theorem infvalley_LPO : (forall f, decr f -> exists x, infvalley f x) -> LPO.
Proof.
  intros IV f.
  destruct (IV (f_down_nat f) (f_down_nat_decr f)) as (x & V).
  destruct (f_down_nat f x) eqn:F.
  - apply f_down_nat_0_elim in F.
    firstorder.
  - specialize (f_down_nat_S_elim _ _ _ F).
    clear F. intros F.
    right.
    intros z.
    destruct (le_lt_dec z x).
    + auto.
    + assert (f_down_nat f z = f_down_nat f x) by auto with *.
      rewrite f_down_nat_S_intro with (x := x) in H.
      * eauto using f_down_nat_S_elim.
      * auto.
Qed.

Lemma LPO_decide_lt : LPO -> forall f, decr f -> forall n, (exists x, f x < n) \/ (forall x, f x >= n).
Proof.
  unfold LPO.
  intros LPO f D n.
  destruct (LPO (fun x => Nat.ltb (f x) n)) as [(x & H)|].
  * apply Nat.ltb_lt in H. eauto.
  * right. intro x. specialize (H x). apply Nat.ltb_ge in H. omega.
Qed.

Lemma magic_induction : LPO -> forall f, decr f -> forall y x, f x <= y -> exists x', infvalley f x'.
Proof.
  unfold LPO.
  intros LPO f D.
  induction y; intros x B.
  - exists x. intros y Hy. assert (f y <= f x) by auto using decr_trans. omega.
  - destruct (LPO_decide_lt LPO f D (S y)) as [(x' & Hx')|LB].
    + eauto with arith.
    + exists x. intros z Hz.
      assert (f z <= f x) by auto using decr_trans.
      assert (f z >= S y) by auto.
      omega.
Qed.

Theorem LPO_infvalley : LPO -> forall f, decr f -> exists x, infvalley f x.
Proof.
  unfold LPO.
  intros LPO f D.
  exact (magic_induction LPO f D (f 0) 0 ltac:(omega)).
Qed.