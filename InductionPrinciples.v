Require Import List.
Import ListNotations.
Require Import Lia.

Set Implicit Arguments.

Module foo.

Inductive tree A := leaf | branch : tree A -> A -> tree A -> tree A.
Arguments leaf {_}.

Check tree_ind.
Print tree_ind.

Fixpoint tree_to_list {A} (t : tree A) : list A :=
  match t with
  | leaf => []
  | branch l d r => tree_to_list l ++ [d] ++ tree_to_list r
  end.

Fixpoint tree_ind' {A} (P : tree A -> Prop)
         (P_leaf : P leaf)
         (P_branch : forall l x r, P l -> P r -> P (branch l x r))
         (t : tree A) : P t :=
  match t with
  | leaf => P_leaf
  | branch l x r => P_branch l x r
                            (tree_ind' P P_leaf P_branch l)
                            (tree_ind' P P_leaf P_branch r)
  end.

(*
  destruct t.
  - apply P_leaf.
  - apply P_branch.
    + apply tree_ind'.
      apply P_leaf.
      apply P_branch.
    + apply tree_ind'.
      apply P_leaf.
      apply P_branch.
*)

(*
  refine (match t with
          | leaf => _
          | branch l x r => _
          end).
  - refine P_leaf.
  - refine (P_branch l x r _ _).
    + refine (tree_ind' A P P_leaf P_branch l).
    + refine (tree_ind' A P P_leaf P_branch r).
*)


Definition tree_ind'' {A}
           (P : tree A -> Prop)
           (P_leaf : P leaf)
           (P_branch : forall l x r, P l -> P r -> P (branch l x r)) :=
  fix go (t : tree A) : P t :=
    match t with
    | leaf => P_leaf
    | branch l x r => P_branch l x r (go l) (go r)
    end.

Check tree_ind.
Check tree_ind'.
Check tree_ind''.
End foo.


Fixpoint list_sum (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => x + list_sum xs'
  end.

Lemma list_sum_append :
  forall xs ys,
    list_sum (xs ++ ys) = list_sum xs + list_sum ys.
Proof.
  intros.
  induction xs; simpl; lia.
Qed.



Module mutual.

Inductive tree A := node : A -> forest A -> tree A
with forest A := empty | grow : tree A -> forest A -> forest A.
Arguments empty {_}.

Check tree_ind.
Check forest_ind.


Section tree_ind'.
  Variable A : Type.
  Variable P_tree : tree A -> Prop.
  Variable P_forest : forest A -> Prop.

  Variable P_tree_node : forall a f, P_forest f -> P_tree (node a f).
  Variable P_forest_empty : P_forest empty.
  Variable P_forest_grow : forall t f, P_tree t -> P_forest f -> P_forest (grow t f).

  Fixpoint tree_ind' (t : tree A) : P_tree t :=
    match t with
    | node a f => P_tree_node a (*f*) (forest_ind' f)
    end
  with forest_ind' (f : forest A) : P_forest f :=
    match f with
    | empty => P_forest_empty
    | grow t f' => P_forest_grow (tree_ind' t) (forest_ind' f')
    end
  .

  Definition tree_forest_ind := conj tree_ind' forest_ind'.

End tree_ind'.

Fixpoint tree_sum (t : tree nat) : nat :=
  match t with
  | node n f => n + forest_sum f
  end
with forest_sum (f : forest nat) : nat :=
  match f with
  | empty => 0
  | grow t f' => tree_sum t + forest_sum f'
  end.

Fixpoint tree_flatten {A} (t : tree A) : list A :=
  match t with
  | node a f => a :: forest_flatten f
  end
with forest_flatten {A} (f : forest A) : list A :=
  match f with
  | empty => []
  | grow t f' => tree_flatten t ++ forest_flatten f'
  end.

(*
Theorem tree_flatten_sum :
  forall t,
    tree_sum t = list_sum (tree_flatten t)
with forest_flatten_sum :
  forall f,
    forest_sum f = list_sum (forest_flatten f).
*)


Theorem tree_forest_flatten_sum :
  (forall t, tree_sum t = list_sum (tree_flatten t)) /\
  (forall f, forest_sum f = list_sum (forest_flatten f)).
Proof.
  apply tree_forest_ind; intros; simpl.
  - lia.
  - lia.
  - rewrite list_sum_append. lia.
Qed.

Theorem tree_flatten_sum :
  forall t,
    tree_sum t = list_sum (tree_flatten t).
Proof.
  intros t.
  induction t using tree_ind'
  with (P_forest := fun f => forest_sum f = list_sum (forest_flatten f));
    simpl.
  - lia.
  - lia.
  - rewrite list_sum_append. lia.
Qed.

End mutual.


Inductive tree A := node : A -> list (tree A) -> tree A.

Check tree_ind.

Section tree_ind'.
  Variable A : Type.
  Variable P_tree : tree A -> Prop.
  Variable P_list : list (tree A) -> Prop.

  Variable P_tree_node : forall a l, P_list l -> P_tree (node a l).
  Variable P_list_nil : P_list [].
  Variable P_list_cons : forall t l, P_tree t -> P_list l -> P_list (t :: l).

  Fixpoint tree_ind' (t : tree A) : P_tree t :=
    let fix tree_list_ind' (l : list (tree A)) : P_list l :=
        match l with
        | [] => P_list_nil
        | t :: l' => P_list_cons (tree_ind' t) (tree_list_ind' l')
        end
    in
    match t with
    | node a l => P_tree_node a (*f*) (tree_list_ind' l)
    end
  .

  Definition tree_list_ind' :=
    fix tree_list_ind' (l : list (tree A)) : P_list l :=
      match l with
      | [] => P_list_nil
      | t :: l' => P_list_cons (tree_ind' t) (tree_list_ind' l')
      end.

  Definition tree_forest_ind := conj tree_ind' tree_list_ind'.
End tree_ind'.

Fixpoint tree_sum (t : tree nat) : nat :=
  let fix tree_list_sum (l : list (tree nat)) : nat :=
      match l with
      | [] => 0
      | t :: l' => tree_sum t + tree_list_sum l'
      end
  in
  match t with
  | node n l => n + tree_list_sum l
  end.

Definition tree_list_sum : list (tree nat) -> nat :=
  fix tree_list_sum (l : list (tree nat)) : nat :=
    match l with
    | [] => 0
    | t :: l' => tree_sum t + tree_list_sum l'
    end.

Fixpoint tree_flatten {A} (t : tree A) : list A :=
  match t with
  | node n l => n :: flat_map tree_flatten l
  end.


(*

Definition f_helper := (fun a b => ...).
Definition f := List.fold_left f_helper z.

forall l, List.fold_left f_helper z l = ...
*)


Theorem tree_flatten_sum :
  forall t,
    tree_sum t = list_sum (tree_flatten t).
Proof.
  intros.
  induction t using tree_ind'
    with (P_list := fun l => tree_list_sum l = list_sum (flat_map tree_flatten l)); simpl.
  - fold tree_list_sum. lia.
  - lia.
  - rewrite list_sum_append. lia.
Qed.
