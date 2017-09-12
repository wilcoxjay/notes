Definition inj{X Y}(f : X -> Y) := forall x x', f x = f x' -> x = x'.

Definition surj{X Y}(f : X -> Y) := forall y, {x : X & f x = y}.

Fixpoint fin (n : nat) : Type :=
  match n with
  | 0   => False
  | S n => option (fin n)
  end.

Require Fin.

Theorem inj_to_surj(n : nat) : forall f : fin n -> fin n, inj f -> surj f.
Admitted.

Theorem surj_to_inj(n : nat) : forall f : fin n -> fin n, surj f -> inj f.
Admitted.