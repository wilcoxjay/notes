Require Import Relations.Relation_Operators Bool.
Require Vector.

Set Implicit Arguments.

Ltac invc H := inversion H; subst; clear H.

Definition star A (R : A -> A -> Prop) := clos_refl_trans_1n _ R.

Lemma star_refl : forall A (R : A -> A -> Prop) a, star R a a.
Proof. constructor. Qed.
Hint Resolve star_refl.

Lemma star_step : forall A (R : A -> A -> Prop) a1 a2 a3, R a1 a2 -> star R a2 a3 -> star R a1 a3.
Proof. econstructor; eauto. Qed.
Hint Resolve star_step.

Lemma lock_step_sim :
  forall A C (R : A -> C -> Prop) (Sa : A -> A -> Prop) (Sc : C -> C -> Prop),
    (forall a c c', R a c -> Sc c c' -> exists a', Sa a a' /\ R a' c') ->
    forall a c c',
      R a c ->
      star Sc c c' ->
      exists a', star Sa a a' /\ R a' c'.
Proof.
  intros A C R Sa Sc Sim a c c' HR Star.
  generalize dependent a.
  induction Star; intros.
  - eauto.
  - eapply Sim in H; eauto.
    destruct H as (a' & Step & HR').
    apply IHStar in HR'.
    destruct HR' as (a'' & Star' & HR'').
    eauto.
Qed.

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

Lemma star_step_sim :
  forall A C (R : A -> C -> Prop) (Sa : A -> A -> Prop) (Sc : C -> C -> Prop),
    (forall a c c', R a c -> Sc c c' -> exists a', star Sa a a' /\ R a' c') ->
    forall a c c',
      R a c ->
      star Sc c c' ->
      exists a', star Sa a a' /\ R a' c'.
Proof.
  intros A C R Sa Sc Sim a c c' HR Star.
  generalize dependent a.
  induction Star; intros.
  - eauto.
  - eapply Sim in H; eauto.
    destruct H as (a' & Star' & HR').
    apply IHStar in HR'.
    destruct HR' as (a'' & Star'' & HR'').
    eauto.
Qed.

Module system.
  Record t state :=
    Make {
        init : state -> Prop;
        step : state -> state -> Prop
      }.
End system.

Definition local_sys global local := system.t (global * local).

Module global.
  Definition init {G} I (p : G * unit) : Prop :=
    let '(g, tt) := p in I g.

  Definition step G S (p1 p2 : G * unit) : Prop :=
    let '(g1, tt) := p1 in
    let '(g2, tt) := p2 in
    S g1 g2.

  Definition Make {G} s : local_sys G unit :=
    system.Make (init (system.init s)) (step (system.step s)).
End global.

Module parallel.
  Definition init {G L1 L2} I1 I2 (p : G * (L1 * L2)) : Prop :=
    let '(g, (l1, l2)) := p
    in I1 (g, l1) /\ I2 (g, l2).

  Inductive step {G L1 L2} S1 S2 : G * (L1 * L2) -> G * (L1 * L2) -> Prop :=
  | First : forall g g' l1 l1' l2, S1 (g, l1) (g', l1') -> step S1 S2 (g, (l1, l2)) (g', (l1', l2))
  | Second : forall g g' l1 l2 l2', S2 (g, l2) (g', l2') -> step S1 S2 (g, (l1, l2)) (g', (l1, l2'))
  .
  Hint Constructors step.

  Lemma sym : forall G L (S : G * L -> G * L -> Prop) g l1 l2 g' l1' l2',
      step S S (g, (l1, l2)) (g', (l1', l2')) ->
      step S S (g, (l2, l1)) (g', (l2', l1')).
  Proof.
    intros G L S g l1 l2 g' l1' l2' H.
    invc H; econstructor; eauto.
  Qed.

  Lemma star : forall G L1 L2 (S1 : G * L1 -> G * L1 -> Prop) (S2 : G * L2 -> G * L2 -> Prop) g l1 g' l1' l2,
      star S1 (g, l1) (g', l1') ->
      star (step S1 S2) (g, (l1, l2)) (g', (l1', l2)).
  Proof.
    intros G L1 L2 S1 S2 g l1 g' l1' l2 H.
    remember (g, l1) as s.
    remember (g', l1') as s'.
    revert g l1 l1' l2 Heqs Heqs'.
    induction H; intros; subst.
    - invc Heqs'. econstructor.
    - destruct y.
      econstructor.
      econstructor.
      eauto.
      apply IHclos_refl_trans_1n; auto.
  Qed.

  Definition Make {G L1 L2} s1 s2 : local_sys G (L1 * L2) :=
    system.Make (init (system.init s1) (system.init s2))
                (step (system.step s1) (system.step s2)).
End parallel.

Fixpoint parallel_n_ty L (n : nat) : Type :=
  match n with
  | 0 => L
  | S n => L * parallel_n_ty L n
  end.

Fixpoint parallel_n (n : nat) {G L} (s : local_sys G L) : local_sys G (parallel_n_ty L n) :=
  match n with
  | 0 => s
  | S n => parallel.Make s (parallel_n n s)
  end.

Module abstract.
  Definition state := nat.

  Definition init (n : state) : Prop := n = 0.

  Definition step (n n' : state) : Prop := n' = S n.

  Definition thread : local_sys _ _ := global.Make (system.Make init step).

  Definition sys2 := parallel.Make thread thread.
End abstract.

Module concrete.
  Module pc.
    Inductive t :=
    | Lock
    | Read
    | Write (tmp : nat)
    | Unlock
    .
  End pc.

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

  Definition thread : local_sys _ _ := system.Make init step.

  Definition holds (pc : pc.t) : bool :=
    match pc with
    | pc.Read | pc.Write _ | pc.Unlock => true
    | _ => false
    end.

  Definition sys2 := parallel.Make thread thread.

  Definition mutex_thread (s : ((nat * bool) * pc.t)) (other : pc.t) :=
    let '((n, b), pc) := s in
    b = (holds pc || holds other)%bool /\
    (holds pc = false \/ holds other = false).

  Lemma mutex_exchange : forall g pc1 pc2,
      mutex_thread (g, pc1) pc2 <-> mutex_thread (g, pc2) pc1.
  Proof.
    unfold mutex_thread.
    intros [n b] pc1 pc2.
    rewrite orb_comm. rewrite or_comm.
    intuition.
  Qed.

  Lemma mutex_thread_guarantee :
    forall s s' o,
      mutex_thread s o ->
      step s s' ->
      mutex_thread s' o.
  Proof.
    unfold mutex_thread, step.
    intros [[n b] pc] s' o [Hb M].
    destruct pc; intros; subst; simpl in *; try tauto.
    - destruct H. subst. simpl in *. intuition.
    - intuition. discriminate.
  Qed.

  Lemma mutex_thread_rely :
    forall g pc1 pc2 g' pc2',
      mutex_thread (g, pc1) pc2 ->
      step (g, pc2) (g', pc2') ->
      mutex_thread (g', pc1) pc2'.
  Proof.
    intros g pc1 pc2 g' pc2'.
    rewrite !mutex_exchange with (pc1 := pc1).
    apply mutex_thread_guarantee.
  Qed.

  Definition mutex (s : ((nat * bool) * (pc.t * pc.t))) :=
    let '(g, (pc1, pc2)) := s in
    mutex_thread (g, pc1) pc2.

  Lemma mutex_init :
    forall s, parallel.init init init s -> mutex s.
  Proof.
    unfold parallel.init, init.
    intros [g [pc1 pc2]] [].
    inversion 1. inversion 1. subst.
    compute. intuition.
  Qed.

  Lemma mutex_step :
    forall s s',
      mutex s ->
      parallel.step step step s s' ->
      mutex s'.
  Proof.
    unfold mutex.
    intros [g [pc1 pc2]] s' M Step.
    invc Step.
    - eauto using mutex_thread_guarantee.
    - eauto using mutex_thread_rely.
  Qed.
End concrete.

Definition right G L (S : _ -> _ -> Prop) (I : _ -> Prop) l1 :=
  forall (g g' g'' : G) (l1' l2 l2' : L),
    I (g, (l1, l2)) ->
    S (g, l1) (g', l1') ->
    S (g', l2) (g'', l2') ->
    exists g0,
      S (g, l2) (g0, l2') /\
      S (g0, l1) (g', l1').

Definition left G L (S : _ -> _ -> Prop) (I : _ -> Prop) l2 :=
  forall (g g' g'' : G) (l1 l1' l2' : L),
    I (g, (l1, l2)) ->
    S (g, l1) (g', l1') ->
    S (g', l2) (g'', l2') ->
    exists g0,
      S (g, l2) (g0, l2') /\
      S (g0, l1) (g', l1').

Ltac right_crush :=
  intros [n b] [n' b'] g'' pc' pc2 pc2';
  compute;
  destruct pc2 eqn:?; intuition (try (discriminate || congruence)).

Ltac left_crush :=
  intros [n b] [n' b'] g'' pc pc2 pc2';
  compute;
  destruct pc; intuition (try (discriminate || congruence)).

Lemma lock_right :
  right concrete.step concrete.mutex concrete.pc.Lock.
Proof.
  right_crush.
Qed.

Lemma unlock_left :
  left concrete.step concrete.mutex concrete.pc.Unlock.
Proof.
  left_crush.
Qed.

Lemma read_right :
  right concrete.step concrete.mutex concrete.pc.Read.
Proof.
  right_crush.
Qed.

Lemma read_left :
  left concrete.step concrete.mutex concrete.pc.Read.
Proof.
  left_crush.
Qed.

Lemma write_right :
  forall n,
    right concrete.step concrete.mutex (concrete.pc.Write n).
Proof.
  intros n0.
  right_crush.
Qed.

Lemma write_left :
  forall n,
    left concrete.step concrete.mutex (concrete.pc.Write n).
Proof.
  intros n0.
  left_crush.
Qed.

Module simulation.
  Definition thread (a : nat * unit) (c : (nat * bool) * concrete.pc.t) : Prop :=
    let '(an, tt) := a in
    let '((cn, b), pc) := c in
    match pc with
    | concrete.pc.Write n => n = cn
    | _ => True
    end.

  Definition sys (a : nat * (unit * unit)) (c : (nat * bool) * (concrete.pc.t * concrete.pc.t)) : Prop :=
    let '(an, (tt, tt)) := a in
    let '((cn, b), (l1, l2)) := c in
    an = cn /\
    thread (an, tt) ((cn, b), l1) /\
    thread (an, tt) ((cn, b), l2) /\
    concrete.mutex ((cn, b), (l1, l2)).

  Lemma sys_inj :
    forall an u1 u2 cn b l1 l2,
      sys (an, (u1, u2)) ((cn, b), (l1, l2)) ->
      an = cn.
  Proof.
    intros an [] []. compute. intuition.
  Qed.
End simulation.


Lemma increasing_abstract_step :
  forall n u n' u',
    system.step abstract.thread (n, u) (n', u') ->
    n <= n'.
Proof.
  compute.
  intros n [] n' [] H.
  subst. auto.
Qed.

Lemma increasing_abstract_step2 :
  forall n u n' u',
    system.step abstract.sys2 (n, u) (n', u') ->
    n <= n'.
Proof.
  intros n u n' u' H.
  invc H; eauto using increasing_abstract_step.
Qed.

Theorem increasing_abstract :
  forall n u n' u',
    star (system.step abstract.sys2) (n, u) (n', u') ->
    n <= n'.
Proof.
  intros n u n' u' H.
  remember (n, u) as s.
  remember (n', u') as s'.
  revert n u Heqs n' u' Heqs'.
  induction H; intros; subst.
  - invc Heqs'. auto.
  - destruct y as [n0 u0].
    eauto using PeanoNat.Nat.le_trans, increasing_abstract_step2.
Qed.

Lemma sim :
  forall n b pc n' b' pc',
    simulation.thread (n, tt) (n, b, pc) ->
    system.step concrete.thread (n, b, pc) (n', b', pc') ->
    simulation.thread (n', tt) (n', b', pc') /\
    star (system.step abstract.thread) (n, tt) (n', tt).
Proof.
  intros n b pc n' b' pc'.
  destruct pc; simpl; intuition;
    match goal with
    | [ H : (_, _) = (_, _) |- _ ] => invc H
    end; auto.

  econstructor; [|apply star_refl]. reflexivity.
Qed.

Theorem increasing_concrete :
  forall n n' b' pc1' pc2',
    star (system.step concrete.sys2)
         ((n, false), (concrete.pc.Lock, concrete.pc.Lock))
         ((n', b'), (pc1', pc2')) ->
    n <= n'.
Proof.
  intros n n' b' pc1' pc2' Star.
  apply star_step_sim with (R := simulation.sys) (a := (n, (tt, tt)))
                                                 (Sa := system.step abstract.sys2) in Star.
  - destruct Star as ([n0 [[] []]] & Star & Sim).
    apply simulation.sys_inj in Sim. subst n0.
    eauto using increasing_abstract.
  - clear n n' b' pc1' pc2' Star.
    intros [an [[] []]] [[cn b] [pc1 pc2]] [[cn' b'] [pc1' pc2']] (? & Sim1 & Sim2 & M) Step.
    invc Step.
    + rename pc2' into pc2.
      destruct (sim _ _ _ _ _ _ Sim1 H1).
      exists (cn', (tt, tt)).
      split.
      * apply parallel.star. auto.
      * split; auto.
        split; auto.
        split.
        -- destruct pc1, pc2; simpl in *; intuition (try (discriminate || congruence)).
        -- eapply concrete.mutex_step; eauto.
    + rename pc1' into pc1.
      destruct (sim _ _ _ _ _ _ Sim2 H1).
      exists (cn', (tt, tt)).
      split.
      * apply parallel.star. auto.
      * split; auto.
        split; auto.
        -- destruct pc1, pc2; simpl in *; intuition (try (discriminate || congruence)).
        -- split; auto.
           eapply concrete.mutex_step; eauto.
  - compute. intuition.
Qed.
