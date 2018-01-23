Require Import List Omega Arith.
Import ListNotations.

Section tree.

  Variable A : Type.

  Inductive t :=
  | leaf
  | node (x : A) (t1 t2 : t)
  .

  Fixpoint indexed_preorder i t :=
    match t with
    | leaf => []
    | node x l r => (i, x) :: indexed_preorder (false :: i) l ++ indexed_preorder (true :: i) r
    end.

  Fixpoint insert (i : list bool) (x : t) t {struct t} :=
    match t with
    | leaf => x
    | node y l r =>
      match i with
      | [] => t (* bogus *)
      | false :: i => node y (insert i x l) r
      | true :: i => node y l (insert i x r)
      end
    end.

  Lemma insert_leaf :
    forall t i,
      insert i leaf t = t.
  Proof.
    intros t; induction t; simpl; intros i.
    - auto.
    - destruct i as [|[]]; f_equal; auto.
  Qed.

  Fixpoint insertable i t {struct t} :=
    match t with
    | leaf => i = []
    | node y l r =>
      match i with
      | [] => False
      | false :: i => insertable i l
      | true :: i => insertable i r
      end
    end.

  Fixpoint unpreorder t l :=
    match l with
    | [] => t
    | (i, x) :: l => unpreorder (insert (rev i) (node x leaf leaf) t) l
    end.

  Lemma insert_insert : forall r a b i1 i2,
      insertable i1 r ->
      insert i1 (insert i2 b a) r = insert (i1 ++ i2) b (insert i1 a r).
  Proof.
    induction r; simpl; intros a b i1 i2 I.
    - now subst i1. 
    - destruct i1 as [|[]].
      + intuition.
      + now rewrite IHr2 by assumption.
      + now rewrite IHr1 by assumption.
  Qed.

  Lemma insertable_insert :
  forall r i1 i2 a,
    insertable i1 r ->
    insertable i2 a ->
    insertable (i1 ++ i2) (insert i1 a r).
  Proof.
    induction r; simpl; intros i1 i2 a I1 I2.
    - now subst.
    - destruct i1 as [|[]]; simpl; intuition.
  Qed.

  Lemma unpreorder_preorder_id :
    forall a r i l,
      insertable (rev i) r ->
      unpreorder r (indexed_preorder i a ++ l) = unpreorder (insert (rev i) a r) l.
  Proof.
    induction a; simpl; intros r i l I.
    - now rewrite insert_leaf.
    - rewrite app_ass.
      rewrite IHa1 by (simpl; apply insertable_insert; simpl; auto).
      simpl.
      rewrite <- insert_insert by assumption.
      simpl.
      rewrite IHa2 by (simpl; apply insertable_insert; simpl; auto).
      simpl.
      rewrite <- insert_insert by assumption.
      reflexivity.
  Qed.

End tree.