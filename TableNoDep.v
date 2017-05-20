Require Import List.
Import ListNotations.

Set Implicit Arguments.

Inductive ilist (A : Type) (B : Type) : list A -> Type :=
| inil : ilist B []
| icons : forall a (b : B) l (h : ilist B l), ilist B (a :: l).

Definition table (A R C : Type) (r : list R) (c : list C) : Type :=
  ilist (ilist A c) r.

Inductive member (A : Type) (x : A) : list A -> Type :=
| here : forall l, member x (x :: l)
| there : forall y l, member x l -> member x (y :: l).
Arguments here {_} {_} {_}.
Arguments there {_} {_} {_} {_} _.

Fixpoint iget A B (x : A) (l : list A) (m : member x l) : ilist B l -> B :=
  match m with
  | here =>
    fun h => match h with
          | inil _ _ => I
          | icons _ b _ => b
          end
  | there m =>
    fun h => match h with
          | inil _ _ => I
          | icons _ _ h => fun rec => rec h
          end (iget m)
  end.

Definition lookup A R C (r : list R) (c : list C) (t : table A r c) x y
           (mx : member x r) (my : member y c) : A :=
  iget my (iget mx t).
