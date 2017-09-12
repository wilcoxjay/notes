Require Vector.
Require Import List.
Import ListNotations.


Inductive hlist {A : Type} (B : A -> Type) : list A -> Type :=
| hnil : hlist B [ ]
| hcons : forall a l, B a -> hlist B l -> hlist B (a :: l).
Arguments hnil {_ _}.
Arguments hcons {_ _ _ _} _ _.

Definition vector_of_vectors (T : Type) (l : list nat) : Type :=
  hlist (Vector.t T) l.

Section example.
  Definition ls : list nat := [2; 0; 1].

  Definition v : vector_of_vectors bool ls :=
    hcons [false; true]
          (hcons []
                 (hcons [true] hnil)).
End example.