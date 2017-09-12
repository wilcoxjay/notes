Require Import Coq.Relations.Relation_Definitions RelationClasses Arith Omega.

Set Implicit Arguments.

Class TotalOrder A (R : relation A) := {
  TotalOrder_strict :> StrictOrder R;
  TotalOrder_trichotomy : forall x y : A, R x y \/ x = y \/ R y x
}.

Instance nat_StrictOrder : StrictOrder lt.
constructor.
- red. red. intros n. red. apply Nat.lt_irrefl.
- red. apply Nat.lt_trans.
Defined.

Instance nat_TotalOrder : TotalOrder lt.
constructor.
- exact nat_StrictOrder.
- intros x y. omega.
Defined.
