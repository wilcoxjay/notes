Definition streamless(X : Set) := forall f : nat -> X,
  {i : nat & { j : nat | i <> j /\ f i = f j}}.

Theorem streamless_prod : forall X Y, streamless X -> streamless Y -> streamless (X * Y).
Proof.
  intros X Y SX SY f.


Theorem streamless_sum : forall X Y, streamless X -> streamless Y -> streamless (X + Y).
Proof.
  intros X Y SX SY f.
  destruct (f 0) eqn:H.
  - set (g := fun n => match f n with
                    | inl x0 => x0
                    | _ => x
                    end).
    destruct (SX g) as [gi [gj [N Hg]]].
    subst g. simpl in Hg.
    destruct (f gi) eqn:Hi; destruct (f gj) eqn:Hj.
    + exists gi, gj. intuition congruence.
    + set (h := fun n => match f n with
                      | inl x0 => (x0, y)
                      | inr y0 => (x, y0)
                      end).
      destruct (
  -

  Definition injective {A B} (g : A -> B) : Prop :=
    (forall x y, g x = g y -> x = y).

  Definition stream_splits {A B C} (f : A -> B) (k : C -> B) : Prop :=
    exists (g : A -> A) (h : A -> C), injective g /\ (forall n, f (g n) = k (h n)).

  Lemma sum_stream_split : forall X Y (f : nat -> X + Y),
      stream_splits f inl \/
      stream_splits f inr.

Admitted.