Require Import Arith List Omega.
Require Import Permutation.
Require String.
Import ListNotations.
Set Implicit Arguments.

Notation id_l f x := (forall y, f x y = y).
Notation comm f := (forall x y, f x y = f y x).
Notation assoc f := (forall x y z, f x (f y z) = f (f x y) z).
Notation distr f g := (forall x y z, f x (g y z) = g (f x y) (f x z)).
Notation eq_dec A := (forall x y : A, {x = y} + {x <> y}).

(*
Definition remove_all A (A_eq_dec : eq_dec A) (a : A) :=
  fix go (xs : list A) : list A :=
    match xs with
    | [] => []
    | x :: xs => if A_eq_dec a x then go xs else a :: go xs
    end.
*)

Lemma NoDup_filter :
  forall A (f : A -> bool) l,
    NoDup l ->
    NoDup (filter f l).
Proof.
  induction 1; simpl.
  - constructor.
  - destruct (f x) eqn:E; auto.
    constructor; auto.
    intro C.
    rewrite filter_In in C.
    intuition.
Qed.

Lemma NoDup_app :
  forall A (l1 l2 : list A),
    NoDup l1 ->
    NoDup l2 ->
    (forall x, In x l1 -> In x l2 -> False) ->
    NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 ND1.
  induction ND1; intros ND2 I; simpl.
  - exact ND2.
  - constructor.
    + rewrite in_app_iff.
      intro C.
      destruct C as [C|C].
      * auto.
      * apply I with (x0 := x); simpl; auto.
    + apply IHND1.
      * assumption.
      * intros x' Ix' Iy.
        apply I with (x0 := x'); simpl; auto.
Qed.

Lemma NoDup_map_inj :
  forall A B (f : A -> B) (l : list A),
    (forall x y, f x = f y -> x = y) ->
    NoDup l ->
    NoDup (map f l).
Proof.
  induction 2; simpl; constructor.
  - rewrite in_map_iff.
    intros [x' [F I]].
    assert (x' = x) by eauto.
    subst x'.
    contradiction.
  - auto.
Qed.

Lemma NoDup_list_prod :
  forall A B (l1 : list A) (l2 : list B),
    NoDup l1 ->
    NoDup l2 ->
    NoDup (list_prod l1 l2).
Proof.
  induction 1; intros ND.
  - constructor.
  - simpl.
    apply NoDup_app.
    + apply NoDup_map_inj; [|assumption].
      intros. congruence.
    + now auto.
    + intros [a b].
      rewrite in_map_iff.
      intros [b' [E I]].
      inversion E; subst; clear E.
      rewrite in_prod_iff.
      intros [C _].
      contradiction.
Qed.

Module Type USEMIRING.
  Parameter t : Type.

  Parameter t_eq_dec : eq_dec t.

  (* semiring operations and axioms *)

  Parameter zero : t.
  Parameter one : t.
  Parameter plus : t -> t -> t.
  Parameter mult : t -> t -> t.

  Notation "0" := zero.
  Notation "1" := one.
  Notation "x + y" := (plus x y) (at level 50, left associativity).
  Notation "x * y" := (mult x y) (at level 40, left associativity).

  Parameter plus_comm : comm plus.
  Parameter plus_assoc : assoc plus.
  Parameter plus_zero_l : id_l plus 0.

  Parameter mult_comm : comm mult.
  Parameter mult_assoc : assoc mult.
  Parameter mult_one_l : id_l mult 1.
  Parameter mult_zero_l : forall x, 0 * x = 0.

  Parameter mult_plus_distr : distr mult plus.


  (* squash and axioms *)

  Parameter squash : t -> t.

  Parameter squash_zero : squash 0 = 0.
  Parameter squash_one : squash 1 = 1.

  Parameter squash_plus_l : forall x y, squash (squash x + y) = squash (x + y).
  Parameter squash_mult : forall x y, squash (x * y) = squash x * squash y.
  Parameter squash_mult_idem : forall x, squash x * squash x = squash x.

  Parameter idem_are_squash : forall x, x * x = x -> squash x = x.


  (* not and axioms *)

  Parameter not : t -> t.

  Parameter not_zero : not 0 = 1.

  Parameter not_mult : forall x y, not (x * y) = squash (not x + not y).
  Parameter not_plus : forall x y, not (x + y) = not x * not y.

  Parameter not_squash : forall x, not (squash x) = squash (not x).

  Parameter not_is_squash : forall x, squash (not x) = not x.
End USEMIRING.

Module UsemiringSum (U : USEMIRING).
  Include U.

  Fixpoint sum' D (f : D -> t) (l : list D) : t :=
    match l with
    | [] => zero
    | d :: l => plus (f d) (sum' f l)
    end.

  Lemma sum'_plus : forall D (f1 f2 : D -> t) l,
      sum' (fun d => f1 d + f2 d) l = sum' f1 l + sum' f2 l.
  Proof.
    induction l; simpl.
    - now rewrite plus_zero_l.
    - rewrite IHl.
      rewrite !plus_assoc.
      f_equal.
      rewrite <- !plus_assoc.
      f_equal.
      apply plus_comm.
  Qed.

  Lemma sum'_zero :
    forall D (l : list D),
      sum' (fun _ : D => 0) l = 0.
  Proof.
    induction l; simpl.
    - reflexivity.
    - now rewrite U.plus_zero_l.
  Qed.

  Lemma sum'_sum' : forall D1 D2 (f : D1 -> D2 -> t) l1 l2,
      sum' (fun d1 => sum' (fun d2 => f d1 d2) l2) l1 = sum' (fun d2 => sum' (fun d1 => f d1 d2) l1) l2.
  Proof.
    induction l1; simpl; intros l2.
    - now rewrite sum'_zero.
    - rewrite IHl1.
      clear.
      induction l2; simpl.
      + now rewrite U.plus_zero_l.
      + rewrite <- !plus_assoc.
        f_equal.
        rewrite <- IHl2.
        rewrite !plus_assoc.
        f_equal.
        apply plus_comm.
  Qed.

  Lemma sum'_mult : forall D (f : D -> t) x l,
      sum' (fun d => x * f d) l = x * sum' f l.
  Proof.
    induction l; simpl.
    - now rewrite mult_comm, mult_zero_l.
    - now rewrite IHl, U.mult_plus_distr.
  Qed.

  Definition contains_support D (f : D -> t) (l : list D) : Prop :=
    forall x, ~ In x l -> f x = 0.

  Definition wf D (f : D -> t) :=
    { l : list D | NoDup l /\ contains_support f l }.

  Definition sum D (f : D -> t) (pf : wf f) : t :=
    sum' f (proj1_sig pf).
  Arguments sum {_} _ _.

  Definition support D (f : D -> t) :=
    filter (fun d => if U.t_eq_dec (f d) 0 then false else true).

  Lemma sum_support : forall D (f : D -> t) l, sum' f l = sum' f (support f l).
  Proof.
    induction l; simpl.
    - reflexivity.
    - destruct U.t_eq_dec as [E|E].
      + now rewrite E, plus_zero_l.
      + simpl. congruence.
  Qed.

  Lemma support_nil :
    forall D (f : D -> t),
      (forall d, f d = 0) ->
      forall l, support f l = [].
  Proof.
    induction l; simpl.
    - reflexivity.
    - destruct (U.t_eq_dec (f a) 0).
      + assumption.
      + rewrite H in n. congruence.
  Qed.

  Lemma NoDup_support :
    forall D (f : D -> t) l,
      NoDup l ->
      NoDup (support f l).
  Proof.
    intros D f l H.
    now apply NoDup_filter.
  Qed.

  Lemma contains_support_Permutation_support :
    forall D (f : D -> t) (D_eq_dec : eq_dec D) l1 l2,
      contains_support f l1 ->
      contains_support f l2 ->
      NoDup l1 ->
      NoDup l2 ->
      Permutation (support f l1) (support f l2).
  Proof.
    intros D f D_eq_dec l1 l2 CS1 CS2 ND1 ND2.
    apply NoDup_Permutation;
    auto using NoDup_support.
    clear ND1 ND2.
    revert l1 l2 CS1 CS2.
    cut (forall l1 l2 : list D,
            contains_support f l1 ->
            contains_support f l2 ->
            forall x : D, In x (support f l1) -> In x (support f l2)); [now firstorder|].
    unfold support.
    intros l1 l2 CS1 CS2 x I.
    apply filter_In.
    apply filter_In in I.
    destruct I as [I H].
    destruct U.t_eq_dec as [|E]; try discriminate.
    split; [|reflexivity].
    destruct (in_dec D_eq_dec x l2); [assumption|].
    exfalso.
    apply E.
    now apply CS2.
  Qed.

  Lemma sum'_Permutation : forall D (f : D -> t) l1 l2,
      Permutation l1 l2 ->
      sum' f l1 = sum' f l2.
  Proof.
    induction 1; simpl; auto using f_equal2.
    - rewrite !plus_assoc.
      now rewrite plus_comm with (x := f y).
    - congruence.
  Qed.

  Lemma sum_irrel :
    forall D (D_eq_dec : eq_dec D) (f : D -> t) (pf1 pf2 : wf f),
      sum f pf1 = sum f pf2.
  Proof.
    destruct pf1 as [l1 [ND1 WF1]], pf2 as [l2 [ND2 WF2]].
    unfold sum.
    simpl.

    rewrite sum_support.
    rewrite sum_support with (l := l2).

    now rewrite sum'_Permutation with (l2 := support f l2)
    by auto using contains_support_Permutation_support.
  Qed.

  Lemma contains_support_nodup :
    forall D (D_eq_dec : eq_dec D) (f : D -> t) l,
      contains_support f l ->
      contains_support f (nodup D_eq_dec l).
  Proof.
    unfold contains_support.
    intros D D_eq_dec f l L x I.
    now rewrite nodup_In in I; auto.
  Qed.

  Lemma wf_plus :
    forall D (f g : D -> t),
      eq_dec D ->
      wf f ->
      wf g ->
      wf (fun t => plus (f t) (g t)).
  Proof.
    intros D f g D_eq_dec [l1 [ND1 CS1]] [l2 [ND2 CS2]].
    exists (nodup D_eq_dec (l1 ++ l2)).
    split.
    - apply NoDup_nodup.
    - apply contains_support_nodup.
      unfold contains_support in *.
      intros x I.
      rewrite in_app_iff in I.
      firstorder.
      now rewrite CS1, CS2, plus_zero_l by assumption.
  Qed.

  Lemma wf_mult1 :
    forall D (f g : D -> t),
      wf f ->
      wf (fun t => mult (f t) (g t)).
  Proof.
    intros D f g [l [ND CS]].
    exists l.
    split; [assumption|].
    intros x I.
    unfold contains_support in CS.
    rewrite CS by assumption.
    now rewrite U.mult_zero_l.
  Defined.

  Lemma wf_mult2 :
    forall D (f g : D -> t),
      wf g ->
      wf (fun t => mult (f t) (g t)).
  Proof.
    intros D f g [l [ND CS]].
    exists l.
    split; [assumption|].
    unfold contains_support in *.
    intros x I.
    rewrite CS by assumption.
    now rewrite mult_comm, mult_zero_l.
  Qed.

  Lemma wf_mult_pair :
    forall D1 D2 (f : D1 -> t) (g : D2 -> t),
      eq_dec D1 ->
      eq_dec D2 ->
      wf f ->
      wf g ->
      wf (fun t => mult (f (fst t)) (g (snd t))).
  Proof.
    intros D1 D2 f g D1_eq_dec D2_eq_dec [l1 [ND1 CS1]] [l2 [ND2 CS2]].
    exists (list_prod l1 l2).
    split.
    - now apply NoDup_list_prod; auto.
    - unfold contains_support in *.
      intros [d1 d2].
      rewrite in_prod_iff.
      intros I.
      simpl.
      destruct (in_dec D1_eq_dec d1 l1), (in_dec D2_eq_dec d2 l2).
      + exfalso. apply I; auto.
      + rewrite CS2 by assumption.
        now rewrite mult_comm, mult_zero_l.
      + rewrite CS1 by assumption.
        now rewrite mult_zero_l.
      + rewrite CS1 by assumption.
        now rewrite mult_zero_l.
  Qed.

  Lemma wf_squash :
    forall D (f : D -> t),
      wf f ->
      wf (fun t => squash (f t)).
  Proof.
    intros D f [l [ND CS]].
    exists l.
    split; auto.
    unfold contains_support in *.
    intros x I.
    rewrite CS by assumption.
    now rewrite squash_zero.
  Qed.

  Lemma sum'_ext :
    forall D (f f' : D -> t) l,
      (forall d, f d = f' d) ->
      sum' f l = sum' f' l.
  Proof.
    induction l; simpl; intros H.
    - reflexivity.
    - rewrite H.
      f_equal.
      now auto.
  Qed.

  Lemma wf_sum1 :
    forall D1 D2 (f : D1 -> D2 -> t) (pf : forall d1, wf (f d1)) l1,
      NoDup l1 ->
      (forall x1 x2, ~ In x1 l1 -> f x1 x2 = 0) ->
      wf (fun d1 => sum (f d1) (pf d1)).
  Proof.
    unfold sum.
    intros D1 D2 f pf l1 ND WF.
    exists l1.
    split; auto.
    red.
    intros x1 I1.
    erewrite sum'_ext with (f' := fun _ => 0).
    now rewrite sum'_zero.
    intros d2.
    now rewrite WF.
  Defined.

  Lemma sum'_interchange :
    forall D1 D2 (f : D1 -> D2 -> t) l1 l2,
      sum' (fun d2 => sum' (fun d1 => f d1 d2) l1) l2 = sum' (fun d1 => sum' (f d1) l2) l1.
  Proof.
    induction l1; simpl; intros l2.
    - apply sum'_zero.
    - rewrite sum'_plus.
      f_equal.
      now auto.
  Qed.

  Lemma sum'_app :
    forall D (f : D -> t) l1 l2,
      sum' f (l1 ++ l2) = sum' f l1 + sum' f l2.
  Proof.
    induction l1; simpl; intros l2.
    - now rewrite plus_zero_l.
    - now rewrite IHl1, plus_assoc.
  Qed.

  Lemma sum'_map :
    forall D1 D2 (f : D2 -> D1) (g : D1 -> t) l2,
      sum' g (map f l2) = sum' (fun d2 => g (f d2)) l2.
  Proof.
    induction l2; simpl.
    - reflexivity.
    - auto using f_equal2.
  Qed.

  Lemma sum'_uncurry :
    forall D1 D2 (f : D1 -> D2 -> t) l1 l2,
      sum' (fun d1 => sum' (f d1) l2) l1 =
      sum' (fun '(d1, d2) => f d1 d2) (list_prod l1 l2).
  Proof.
    induction l1; simpl; intros l2.
    - reflexivity.
    - rewrite sum'_app.
      f_equal.
      + now rewrite sum'_map.
      + now rewrite IHl1.
  Qed.

End UsemiringSum.

Module NatSemiring : USEMIRING.
  Definition t := nat.
  Definition t_eq_dec := eq_nat_dec.

  Definition zero : t := 0.
  Definition one : t := 1.
  Definition plus : t -> t -> t := plus.
  Definition mult : t -> t -> t := mult.

  Notation "0" := zero.
  Notation "1" := one.
  Notation "x + y" := (plus x y) (at level 50, left associativity).
  Notation "x * y" := (mult x y) (at level 40, left associativity).

  Definition plus_comm : comm plus := plus_comm.
  Definition plus_assoc : assoc plus := plus_assoc.
  Definition plus_zero_l : id_l plus 0 := plus_0_l.

  Definition mult_comm : comm mult := mult_comm.
  Definition mult_assoc : assoc mult := mult_assoc.
  Definition mult_one_l : id_l mult 1 := mult_1_l.
  Definition mult_zero_l : forall x, 0 * x = 0 := mult_0_l.

  Definition mult_plus_distr : distr mult plus := Nat.mul_add_distr_l.

  Definition squash : t -> t :=
    fun n =>
    match n with
    | 0 => 0
    | S _ => 1
    end.

  Definition squash_zero : squash 0 = 0 := ltac:(reflexivity).
  Definition squash_one : squash 1 = 1 := ltac:(reflexivity).

  Definition squash_plus_l : forall x y, squash (squash x + y) = squash (x + y).
    unfold squash.
    intros x y.
    destruct x; reflexivity.
  Defined.
  Definition squash_mult : forall x y, squash (x * y) = squash x * squash y.
    unfold squash.
    intros x y.
    destruct x.
    reflexivity.
    simpl.
    destruct y.
    unfold mult.
    rewrite mult_0_r.
    reflexivity.
    reflexivity.
  Defined.
  Definition squash_mult_idem : forall x, squash x * squash x = squash x.
    destruct x; reflexivity.
  Defined.

  Definition idem_are_squash : forall x, x * x = x -> squash x = x.
    intros x H.
    assert (x = 1 \/ x = 0) as E.
    {
      destruct x; [|destruct x]; auto.
      simpl in H.
      exfalso.
      remember (mult x (S (S x))) as y in *.
      clear Heqy.
      omega.
    }
    destruct E as [?|?]; subst; reflexivity.
  Defined.

  (* not and axioms *)

  Definition not : t -> t :=
    fun x =>
    match x with
    | 0 => 1
    | S _ => 0
    end.

  Definition not_zero : not 0 = 1 := ltac:(reflexivity).

  Definition not_mult : forall x y, not (x * y) = squash (not x + not y).
    unfold not, squash.
    destruct x, y; try reflexivity.
    rewrite mult_0_r.
    reflexivity.
  Defined.

  Definition not_plus : forall x y, not (x + y) = not x * not y.
    unfold not.
    destruct x, y; reflexivity.
  Defined.

  Definition not_squash : forall x, not (squash x) = squash (not x).
  unfold not, squash.
  destruct x; reflexivity.
  Defined.

  Definition not_is_squash : forall x, squash (not x) = not x.
  unfold not, squash.
  destruct x; reflexivity.
  Defined.
End NatSemiring.

Inductive Tree (A:Type) :=
| node (t0 t1 : Tree A)
| leaf (a:A)
| empty
.
Arguments empty {_}.

Module type.
Inductive t :=
| int
| bool
| string
.

Fixpoint denote (ty : t) : Type :=
  match ty with
  | int => Z
  | bool => Datatypes.bool
  | string => String.string
  end.

Definition eq_dec ty (x y : denote ty) : {x = y} + {x <> y}.
  destruct ty; simpl in *.
  - apply Z.eq_dec.
  - apply Bool.bool_dec.
  - apply String.string_dec.
Defined.
End type.

Definition Schema := Tree type.t.

Module tuple.
  Fixpoint t (s:Schema) : Type :=
    match s with
    | node t0 t1 => (t t0 * t t1)%type
    | leaf T => type.denote T
    | empty => unit
    end.

  Fixpoint eq_dec s (x y : t s) {struct s} : {x = y} + {x <> y}.
    revert x y.
    refine match s as s0 return Top.eq_dec (t s0) with
           | node s0 s1 => fun x y =>
                            let '(x0, x1) := x in
                            let '(y0, y1) := y in
                            match eq_dec s0 x0 y0, eq_dec s1 x1 y1 with
                            | left _, left _ => left _
                            | _, _ => right _
                            end
           | leaf T => fun x y => type.eq_dec _ x y
           | empty => fun x y => left _
           end; simpl.
    all: try congruence.
    destruct x, y; reflexivity.
  Defined.
End tuple.

Notation "s0 ++ s1" := (node s0 s1).

Module SQL (U : USEMIRING).
Module U := UsemiringSum U.

Section SQL.

  Variable R : Schema -> Type.
  Variable A : type.t -> type.t -> Type.
  Variable C : type.t -> Type.
  Variable U : type.t -> type.t -> Type.
  Variable B : type.t -> type.t -> type.t -> Type.

  Definition Relation s := tuple.t s -> U.t.
  Definition Query Γ s := tuple.t Γ -> Relation s.

  Variable R_denote : forall s, R s -> Relation s.
  Variable A_denote : forall S T, A S T -> (Relation (leaf S) -> type.denote T).
  Variable C_denote : forall S, C S -> type.denote S.
  Variable U_denote : forall S T, U S T -> (type.denote S -> type.denote T).
  Variable B_denote : forall S T U, B S T U -> (type.denote S -> type.denote T -> type.denote U).

  Inductive SQL  : Schema -> Schema -> Type :=
  | table {Γ s} : R s -> SQL Γ s
  | union {Γ s} : SQL Γ s -> SQL Γ s -> SQL Γ s
  | minus {Γ s} : SQL Γ s -> SQL Γ s -> SQL Γ s
  | select  {Γ s} : Pred (Γ ++ s) -> SQL Γ s -> SQL Γ s
  | product {Γ s0 s1} : SQL Γ s0 -> SQL Γ s1 -> SQL Γ (s0 ++ s1)
  | project {Γ s s'} : Proj (Γ ++ s) s' -> SQL Γ s -> SQL Γ s'
  | distinct {Γ s} : SQL Γ s -> SQL Γ s
  | castSQL{Γ Γ' s} : Proj Γ Γ' -> SQL Γ' s -> SQL Γ s

  with Pred : Schema -> Type :=
  | inhabited {Γ s} : SQL Γ s -> Pred Γ
  | equal {Γ T} : Expr Γ T -> Expr Γ T -> Pred Γ
  | negate {Γ} : Pred Γ -> Pred Γ
  | and {Γ} : Pred Γ -> Pred Γ -> Pred Γ
  | or {Γ} : Pred Γ -> Pred Γ -> Pred Γ
  | false {Γ} : Pred Γ
  | true {Γ} : Pred Γ
  | castPred {Γ Γ'} : Proj Γ Γ' -> Pred Γ' -> Pred Γ

  with Proj : Schema -> Schema -> Type :=
  | combine  {Γ Γ0 Γ1} : Proj Γ Γ0 -> Proj Γ Γ1 -> Proj Γ (Γ0 ++ Γ1)
  | left  {Γ0 Γ1} : Proj (Γ0 ++ Γ1) Γ0
  | right  {Γ0 Γ1} : Proj (Γ0 ++ Γ1) Γ1
  | compose  {Γ Γ' Γ''} : Proj Γ Γ' -> Proj Γ' Γ'' -> Proj Γ Γ''
  | star     {Γ} : Proj Γ Γ
  | e2p {T Γ} : Expr Γ T -> Proj Γ (leaf T)
  | erase    {Γ} : Proj Γ empty

  with Expr : Schema -> type.t -> Type :=
  | variable {T Γ} (c:Proj Γ (leaf T)) : Expr Γ T
  | aggregate {Γ S T} : A S T -> SQL Γ (leaf S) -> Expr Γ T
  | constantExpr {Γ S} : C S -> Expr Γ S
  | unaryExpr {Γ S T} : U S T -> Expr Γ S -> Expr Γ T
  | binaryExpr {Γ S T U} : B S T U -> Expr Γ S -> Expr Γ T -> Expr Γ U
  | castExpr {Γ Γ' T} : Proj Γ Γ' -> Expr Γ' T -> Expr Γ T
  .

  Definition R_wf {s} (R : Relation s) := U.wf R.

  Definition Q_wf {Γ s} (Q : Query Γ s) := forall x, R_wf (Q x).

  Hypothesis R_denote_wf : forall s (r : R s), R_wf (R_denote r).

  Arguments existT {_} {_} _ _.

  Local Notation e := existT.

  Fixpoint denoteSQL {Γ s} (a : SQL Γ s) : {q : Query Γ s & Q_wf q}
  with     denotePred {Γ} (slct : Pred Γ) : tuple.t Γ -> U.t
  with     denoteProj {Γ Γ'} (cast: Proj Γ Γ') {struct cast} : tuple.t Γ -> tuple.t Γ'
  with     denoteExpr {Γ T} (e : Expr Γ T) : tuple.t Γ -> type.denote T.
    - unshelve refine (
      match a in SQL Γ s return {q : Query Γ s & Q_wf q} with
      | table r => (e (fun _ => R_denote r) _)
      | union a a' => e (fun g t => U.plus (projT1 (denoteSQL _ _ a) g t) (projT1 (denoteSQL _ _ a') g t)) _
      | minus a a' => e (fun g t => U.mult (projT1 (denoteSQL _ _ a) g t)
                                    (U.not (U.squash (projT1 (denoteSQL _ _ a') g t)))) _
      | select slct a => e (fun g t => U.mult (denotePred _ slct (g, t)) (projT1 (denoteSQL _ _ a) g t)) _
      | product a0 a1 => e (fun g t => U.mult (projT1 (denoteSQL _ _ a0) g (fst t))
                                       (projT1 (denoteSQL _ _ a1) g (snd t))) _
      | project proj a => e (fun g t' =>
          U.sum (fun t => U.mult (projT1 (denoteSQL _ _ a) g t)
                                 (if tuple.eq_dec _ (denoteProj _ _ proj (g, t)) t'
                                  then U.one else U.zero)) _) _
      | distinct a => e (fun g t => U.squash (projT1 (denoteSQL _ _ a) g t)) _
      | castSQL f a => e (fun g t => projT1 (denoteSQL _ _ a) (denoteProj _ _ f g) t) _
      end).
      + apply U.wf_mult1.
        destruct (denoteSQL t t0 a) as [q WF].
        apply WF.
      + intro. apply R_denote_wf.
      + intro.
        apply (U.wf_plus (tuple.eq_dec _)).
        * destruct (denoteSQL s0 s1 a) as [? WF]. apply WF.
        * destruct (denoteSQL s0 s1 a') as [? WF]. apply WF.
      + intro.
        apply U.wf_mult1.
        destruct (denoteSQL s0 s1 a) as [? WF]. apply WF.
      + intro.
        apply U.wf_mult2.
        destruct (denoteSQL t t0 a) as [? WF]. apply WF.
      + intro.
        apply (U.wf_mult_pair (tuple.eq_dec _) (tuple.eq_dec _)).
        * destruct (denoteSQL s0 s1 a0) as [? WF]. apply WF.
        * destruct (denoteSQL s0 s2 a1) as [? WF]. apply WF.
      + intro.
        destruct (denoteSQL t t0 a) as [? WF]. simpl.
        destruct (WF x) as [l [ND CS]].

        exists (nodup (tuple.eq_dec _) (map (fun t1 => (denoteProj (t ++ t0) s0 proj (x, t1))) l)).
        split; [now apply NoDup_nodup|].
        apply U.contains_support_nodup.

        intros t' I.
        rewrite in_map_iff in I.

        unfold U.sum.
        simpl.
        rewrite U.sum'_ext with (f' := fun _ => U.zero).
        now rewrite U.sum'_zero.
        intros d.
        destruct tuple.eq_dec.
        * destruct (in_dec (tuple.eq_dec _) d l).
          -- exfalso. apply I.
             exists d. split; auto.
          -- unfold U.contains_support in CS. rewrite CS by assumption.
             now rewrite U.mult_zero_l.
        * now rewrite U.mult_comm, U.mult_zero_l.
      + intro. apply U.wf_squash.
        destruct (denoteSQL s0 s1 a) as [? WF]. apply WF.
      + intro.
        destruct (denoteSQL s1 s2 a) as [? WF]. apply WF.
    - refine (
      match slct in Pred Γ return tuple.t Γ -> U.t with
      | inhabited a => fun g => U.squash (@U.sum _ (fun t => projT1 (denoteSQL _ _ a) g t) _)
      | equal e0 e1 => fun g => if type.eq_dec _ (denoteExpr _ _ e0 g) (denoteExpr _ _ e1 g)
                            then U.one
                            else U.zero
      | negate slct => fun g => U.not (denotePred _ slct g)
      | and slct0 slct1 => fun g => U.mult (denotePred _ slct0 g) (denotePred _ slct1 g)
      | or slct0 slct1 => fun g => U.squash (U.plus (denotePred _ slct0 g) (denotePred _ slct1 g))
      | false => fun _ => U.zero
      | true => fun _ => U.one
      | castPred f slct => fun g => denotePred _ slct (denoteProj _ _ f g)
      end).
      destruct (denoteSQL s s0 a) as [? WF].
      apply WF.
    - refine (
      match cast in Proj s s' return tuple.t s -> tuple.t s' with
      | combine c c' => fun t => (denoteProj _ _ c t, denoteProj _ _ c' t)
      | left => fst
      | right => snd
      | compose c c' => fun t => denoteProj _ _ c' (denoteProj _ _ c t)
      | star => fun t => t
      | e2p e' => fun t => denoteExpr _ _ e' t
      | erase => fun _ => tt
      end).
    - refine (
      match e in Expr Γ T return tuple.t Γ -> type.denote T with
      | variable c => fun g => denoteProj _ _ c g
      | aggregate aggr a => fun g => A_denote aggr (projT1 (denoteSQL _ _ a) g)
      | constantExpr c => fun _ => C_denote c
      | unaryExpr f e' => fun g => U_denote f (denoteExpr _ _ e' g)
      | binaryExpr f e0 e1 => fun g => B_denote f (denoteExpr _ _ e0 g) (denoteExpr _ _ e1 g)
      | castExpr f e' => fun g => denoteExpr _ _ e' (denoteProj _ _ f g)
      end).
  Defined.
End SQL.
End SQL.

Module NatSQL := SQL NatSemiring.

Print Assumptions NatSQL.denoteSQL.