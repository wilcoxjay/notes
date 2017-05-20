Require Import List.
Import ListNotations.

Set Implicit Arguments.

Inductive hlist (A : Type) (B : A -> Type) : list A -> Type :=
| hnil : hlist B []
| hcons : forall a (b : B a) l (h : hlist B l), hlist B (a :: l).

Definition table (A R C : Type) (r : list R) (c : list C) : Type :=
  hlist (fun _ => hlist (fun _ => A) c) r.

Inductive member (A : Type) (x : A) : list A -> Type :=
| here : forall l, member x (x :: l)
| there : forall y l, member x l -> member x (y :: l).

Fixpoint hget A (B : A -> Type) (x : A) (l : list A) (m : member x l) : hlist B l -> B x :=
  match m with
  | here _ _ =>
    fun h => match h with
          | hnil _ => I
          | hcons _ b _ => b
          end
  | there y m =>
    fun h => match h with
          | hnil _ => I
          | hcons _ _ h => fun rec => rec h
          end (hget m)
  end.

Definition lookup A R C (r : list R) (c : list C) (t : table A r c) x y
           (mx : member x r) (my : member y c) : A :=
  hget my (hget mx t).
