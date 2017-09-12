Require Import Relations.Relation_Operators Bool Omega.
Require Operators_Properties.

Set Implicit Arguments.

Ltac invc H := inversion H; subst; clear H.

Definition star A (R : A -> A -> Prop) := clos_refl_trans_1n _ R.

Lemma star_refl : forall A (R : A -> A -> Prop) a, star R a a.
Proof. constructor. Qed.
Hint Resolve star_refl.

Lemma star_step : forall A (R : A -> A -> Prop) a1 a2 a3, R a1 a2 -> star R a2 a3 -> star R a1 a3.
Proof. econstructor; eauto. Qed.
Hint Resolve star_step.

Lemma star_trans : forall A (R : A -> A -> Prop) a1 a2 a3,
        star R a1 a2 ->
        star R a2 a3 ->
        star R a1 a3.
Proof.
  intros A R a1 a2 a3 H12 H23.
  apply Operators_Properties.clos_rt_rt1n.
  apply Operators_Properties.clos_rt1n_rt in H12.
  apply Operators_Properties.clos_rt1n_rt in H23.
  eauto using rt_trans.
Qed.
Hint Resolve star_trans.

Definition plus A (R : A -> A -> Prop) := clos_trans_1n _ R.

Module n_star.
  Inductive t A (R : A -> A -> Prop) (x : A) : nat -> A -> Prop := 
  | refl : t R x 0 x
  | step : forall y n z, R x y -> t R y n z -> t R x (S n) z
  .
  Hint Constructors t.

  Theorem from_star : forall A (R : A -> A -> Prop) x y, 
      star R x y -> 
      exists n, t R x n y.
  Proof.
    induction 1 as [| ? ? ? HR Step IH].
    - eauto.
    - destruct IH as [n IH]. eauto.
  Qed.

  Lemma to_star : forall A (R : A -> A -> Prop) x n y, 
      t R x n y -> 
      star R x y.
  Proof.
    induction 1; eauto.
  Qed.
End n_star.

Module example.
  Module pc.
    Inductive t :=
    | Lock
    | Read
    | Write (tmp : nat)
    | Unlock
    .
  End pc.

  Module thread.
    Definition state : Type := (nat * bool) * pc.t.
  
    Definition init (s : state) : Prop :=
      s = ((0, false), pc.Lock).
  
    Definition step (s s' : state) : Prop :=
      let '((n, b), pc) := s in
      match pc with
      | pc.Lock => b = false /\ s' = ((n, true), pc.Read)
      | pc.Read => s' = ((n, b), pc.Write n)
      | pc.Write n => s' = ((S n, b), pc.Unlock)
      | pc.Unlock => s' = ((n, false), pc.Lock)
      end.
  End thread.

  Module sys.
    Definition state : Type := (nat * bool) * (pc.t * pc.t).

    Definition get_view1 (s : state) : thread.state :=
      let '((n, b), (pc1, pc2)) := s in
      ((n, b), pc1).

    Definition get_view2 (s : state) : thread.state :=
      let '((n, b), (pc1, pc2)) := s in
      ((n, b), pc2).

    Definition set_view1 (s : state) (s1' : thread.state) : state :=
      let '((_, _), (_, pc2)) := s in
      let '((n, b), pc1) := s1' in
      ((n, b), (pc1, pc2)).

    Definition set_view2 (s : state) (s2' : thread.state) : state :=
      let '((_, _), (pc1, _)) := s in
      let '((n, b), pc2) := s2' in
      ((n, b), (pc1, pc2)).

    Definition init (s : state) : Prop :=
      thread.init (get_view1 s) /\ thread.init (get_view2 s).

    Definition step (s s' : state) : Prop :=
      (exists s1', thread.step (get_view1 s) s1' /\ s' = set_view1 s s1') \/
      (exists s2', thread.step (get_view2 s) s2' /\ s' = set_view2 s s2').

  End sys.
End example.

Definition seq A B C (R1 : A -> B -> Prop) (R2 : B -> C -> Prop) : A -> C -> Prop :=
  fun a c => exists b, R1 a b /\ R2 b c.

Section reduction.
  Variable state : Type.
  Variable init ℛ ℒ : state -> Prop.
  Variable E : state -> state -> Prop.
  Variable M : state -> state -> Prop.

  Hypothesis R_dec : forall s, ℛ s \/ ~ ℛ s.
  Hypothesis L_dec : forall s, ℒ s \/ ~ ℒ s.

  Hypothesis initR : forall s, init s -> ℛ s -> False.
  Hypothesis initL : forall s, init s -> ℒ s -> False.

  Hypothesis ER : forall s s', E s s' -> (ℛ s <-> ℛ s').
  Hypothesis EL : forall s s', E s s' -> (ℒ s <-> ℒ s').

  Hypothesis LMR : forall s s', M s s' -> ℒ s -> ℛ s' -> False.

  Hypothesis RL : forall s, ℛ s -> ℒ s -> False.

  Definition R (s s' : state) : Prop :=
    M s s' /\ ℛ s'.

  Definition L (s s' : state) : Prop :=
    ℒ s /\ M s s'.

  Definition X (s s' : state) : Prop :=
     ~ (ℒ s) /\ M s s' /\ ~ (ℛ s').

  Hypothesis R_comm : forall s x s', R s x -> E x s' -> exists y, E s y /\ R y s'.

  Hypothesis L_comm : forall s x s', E s x -> L x s' -> exists y, L s y /\ E y s'.

  Hypothesis L_nonblocking : forall s, ℒ s -> exists s', star L s s' /\ ~ ℒ s'.

  Definition step s s' := E s s' \/ M s s'.

  Definition 𝒩 s := ~ (ℒ s) /\ ~ (ℛ s).

  Definition M_reduced s s' :=
    𝒩 s /\ plus M s s' /\ 𝒩 s'.

  Definition step_reduced s s' :=
    E s s' \/ M_reduced s s'.

  Require Setoid.

  Lemma R_comm_star :
    forall s1 s2 s3,
      R s1 s2 ->
      star E s2 s3 ->
      exists s,
        star E s1 s /\
        R s s3.
  Proof.
    intros s1 s2 s3 HR Step.
    generalize dependent s1.
    induction Step as [|x s2 s3 HE Step]; intros.
    - eauto.
    - destruct (R_comm HR HE) as (y & HE' & HR').
      destruct (IHStep _ HR') as (s & Star & HR'').
      eauto.
  Qed.

  Lemma L_comm_star :
    forall s1 s2 s3,
      E s1 s2 ->
      star L s2 s3 ->
      exists s,
        star L s1 s /\
        E s s3.
  Proof.
    intros s1 s2 s3 HE Step.
    generalize dependent s1.
    induction Step as [|x s2 s3 HL Step]; intros.
    - eauto.
    - destruct (L_comm HE HL) as (y & HL' & HE').
      destruct (IHStep _ HE') as (s & Star & HR'').
      eauto.
  Qed.

  Lemma L_comm_n_star :
    forall n s1 s2 s3,
      E s1 s2 ->
      n_star.t L s2 n s3 ->
      exists s,
        n_star.t L s1 n s /\
        E s s3.
  Proof.
    intros n s1 s2 s3 HE Step.
    generalize dependent s1.
    induction Step as [|x s2 n s3 HL Step]; intros.
    - eauto.
    - destruct (L_comm HE HL) as (y & HL' & HE').
      destruct (IHStep _ HE') as (s & Star & HR'').
      eauto.
  Qed.

  Lemma L_comm_star_star : 
    forall s1 s2 s3, 
      star E s1 s2 -> 
      star L s2 s3 -> 
      exists s, 
        star L s1 s /\
        star E s s3.
  Proof.
    intros s1 s2 s3 StarE StarL.
    generalize dependent s3.
    induction StarE; intros.
    - eauto.
    - destruct (IHStarE _ StarL) as (s & StarL' & StarE').
      destruct (L_comm_star H StarL') as (s' & StarL'' & H').
      eauto.
  Qed.


  Lemma L_star_not_R :
    forall s s',
      ℒ s ->
      ~ ℒ s' ->
      star L s s' ->
      ~ ℛ s'.
  Proof.
    intros s s' Hs Hs' Star.
    induction Star.
    - intuition.
    - unfold L in H.
      destruct H as [_ HM].
      destruct (L_dec y) as [HLy | HLy].
      + auto.
      + inversion Star.
        * subst. intro. eauto.
        * subst. unfold L in H. intuition.
  Qed.



  Lemma decompose_L :
    forall s n s',
      n_star.t step s n s' ->
      ℒ s ->
      (exists s0 n1 n2,
          n = n1 + n2 /\
          n_star.t L s n1 s0 /\
          n_star.t E s0 n2 s') \/
      (exists s0 n1 n2 ,
          n = n1 + n2 /\
          n_star.t L s n1 s0 /\
          𝒩 s0 /\
          n_star.t step s0 n2 s').
  Proof.
    induction 1 as [|? ? ? ? Step NStar IH]; intros HLx.
    - left. eexists. exists 0, 0. eauto.
    - destruct Step as [HE | HM].
      + assert (HLy : ℒ y) by now rewrite <- EL by eauto.
        destruct (IH HLy) as [(s0 & n1 & n2 & Hn & StarL & StarE) |
                              (s0 & n1 & n2 & Hn & StarL & HN & Rest)]; clear IH.
        * destruct (L_comm_n_star HE StarL) as (s1 & StarL' & HE').
          left. eexists. exists n1, (S n2).
          split; [omega|].
          split; eauto.
        * destruct (L_comm_n_star HE StarL) as (s1 & StarL' & HE').
          right. exists s1, n1, (S n2). split; [omega|].
          intuition eauto.
          -- unfold 𝒩.
             erewrite ER, EL by eauto.
             exact HN.
          -- assert (step s1 s0) by firstorder. 
             eauto. 
      + assert (L x y) by firstorder. 
        destruct (L_dec y) as [HLy | HLy].
        * specialize (IH HLy).
          destruct IH as [(s0 & n1 & n2 & Hn & StarL & StarE) |
                          (s0 & n1 & n2 & Hn & StarL & HN & Rest)].
          -- left. eexists _, (S n1), n2. split; [omega|]. intuition eauto.
          -- right. eexists _, (S n1), n2. split; [omega|]. intuition eauto.
        * assert (~ ℛ y) by (intro; eapply LMR; eauto).
          right. exists y, 1, n. intuition eauto.
          red. auto.
  Qed.

  Lemma EL_star : 
    forall s s', star E s s' -> (ℒ s <-> ℒ s').
  Proof.
    induction 1.
    - intuition.
    - now erewrite EL by eauto.
  Qed.

  Lemma ER_star : 
    forall s s', star E s s' -> (ℛ s <-> ℛ s').
  Proof.
    induction 1.
    - intuition.
    - now erewrite ER by eauto.
  Qed.

  Lemma decompose_R :
    forall s s',
      star step s s' ->
      ℛ s ->
      (exists s0,
          star E s s0 /\
          star R s0 s') \/
      (exists s0 s1 s2 s3,
          star E s s0 /\
          star R s0 s1 /\
          X s1 s2 /\
          star L s2 s3 /\
          star E s3 s') \/
      (exists s0 s1 s2 s3,
          star E s s0 /\
          star R s0 s1 /\
          X s1 s2 /\
          star L s2 s3 /\
          𝒩 s3 /\
          star step s3 s').
  Proof.
    induction 1 as [|? ? ? ? Step IH]; intros HRx.
    - left. exists x. auto.
    - destruct H as [HE | HM].
      + assert (ℛ y) as HRy by now rewrite <- ER by eauto.
        apply IH in HRy.
        destruct HRy as [(s0 & StarE & StarR)| 
                         [(s0 & s1 & s2 & s3 & StarE & StarR & HX & StarL & StarE')|
                          (s0 & s1 & s2 & s3 & StarE & StarR & HX & StarL & HN & Rest)]].
        * left. exists s0. eauto.
        * right. left. exists s0, s1, s2, s3. intuition eauto.
        * right. right. exists s0, s1, s2, s3. intuition eauto.
      + destruct (R_dec y) as [HRy | HRy].
        * assert (HR : R x y) by firstorder.
          specialize (IH HRy).
          destruct IH as [(s0 & StarE & StarR)|
                          [(s0 & s1 & s2 & s3 & StarE & StarR & HX & StarL & StarE')|
                           (s0 & s1 & s2 & s3 & StarE & StarR & HX & StarL & HN & Rest)]].
          -- destruct (R_comm_star HR StarE) as (s' & StarE' & HR').
             left. eauto.
          -- destruct (R_comm_star HR StarE) as (s' & StarE'' & HR').
             right. left. exists s', s1, s2, s3. intuition eauto.
          -- destruct (R_comm_star HR StarE) as (s' & StarE' & HR').
             right. right. exists s', s1, s2, s3. intuition eauto.
        * destruct (L_dec y) as [HLy | HLy].
          -- destruct (decompose_L Step HLy) as [(s0 & StarL & StarE) | (s0 & StarL & HN & Rest)].
             ++ right. left. exists x, x, y, s0.
                intuition.
                red. intuition eauto.
             ++ right. right. exists x, x, y, s0.
                intuition.
                red. intuition eauto.
          -- right. right. exists x, x, y, y. intuition; red; intuition eauto.
  Qed.

  Theorem reduction :
    forall s s',
      star step s s' ->
      𝒩 s ->
      𝒩 s' ->
      star step_reduced s s'.
