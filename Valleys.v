Require Import Omega.

Definition decr(f : nat -> nat) := forall n, f (S n) <= f n.

Definition valley(f : nat -> nat)(n x : nat) := forall y, x <= y -> y <= n+x -> f y = f x.

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

Notation "**" := ltac:(auto) (only parsing).
Notation "***" := ltac:(eauto) (only parsing).
Notation "#" := ltac:(omega) (only parsing).

Lemma valley_or_decrease_within_n :
  forall f x,
    decr f ->
    forall n,
      valley f n x \/ exists x', x <= x' /\ x' < x + n /\ f (S x') < f x'.
Proof.
  intros f x Decr.
  induction n.
  - left. intro z. intros. assert (x = z) by omega. congruence.
  - destruct IHn as [Valley | (x' & Lo & Hi & Fxx')].
    + destruct (eq_nat_dec (f (S (n + x))) (f x)).
      * left. intros z Lo Hi.
        assert (z <= n + x \/ z = S (n + x)) as H by omega; clear Hi.
        destruct H as [Hi|E].
        -- exact (Valley z Lo Hi).
        -- congruence.
      * right.
        exists (n + x). repeat split; try omega.
        pose proof (decr_trans f ** x (S (n + x)) #).
        pose proof (Valley (n + x) # #). omega.
    + right. exists x'. repeat split; try omega.
Qed.

Lemma decr_valleys' :
  forall n f,
    decr f ->
    forall y x k,
      f x <= y ->
      S y * n <= k ->
      exists x, valley f n x.
Proof.
  intros n f Decr.
  induction y; intros x k Bound Y.
  - exists x. intros z Lo Hi. pose proof (decr_trans _ Decr _ _ Lo). omega.
  - destruct (valley_or_decrease_within_n _ x *** n) as [|(x' & Lo & Hi & D)].
    + eauto.
    + apply (IHy (S x') ((x + k) - x')).
      * pose proof (decr_trans _ *** _ _ Lo) as Fxx'. omega.
      * apply plus_le_reg_l with (p := n).
        etransitivity. apply Y. omega.
Qed.

Theorem decr_valleys : forall n f, decr f -> exists x, valley f n x.
Proof.
  intros.
  apply decr_valleys' with (y := f 0) (x := 0) (k := S (f 0) * n); auto.
Qed.