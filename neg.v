Require Import Classical.

Section neg.
  Variable node : Type.
  Variable E : node -> node -> Prop.

  Definition phi : Prop :=
    forall x, exists y, E x y /\ forall z, E y z -> exists u, E z u.

  Definition psi : Prop :=
    exists x, forall y, E x y -> exists z, E y z /\ forall u, ~ E z u.

  Theorem neg : phi <-> ~ psi.
  Proof.
    unfold phi, psi.
    split; intro H.
    - intros [x C].
      destruct (H x) as [y [Exy F]].
      destruct (C y Exy) as [z [Eyz G]].
      destruct (F z Eyz) as [u U].
      apply G with (u := u).
      assumption.
    - intros x.
      apply not_ex_all_not with (n := x) in H.
      apply not_all_ex_not in H.
      destruct H as [y H].
      exists y.
      apply imply_to_and in H.
      destruct H as [Exy H].
      split; [assumption|].
      intros z.
      apply not_ex_all_not with (n := z) in H.
      apply not_and_or in H.
      firstorder.
      apply not_all_not_ex in H.
      assumption.
  Qed.
End neg.




