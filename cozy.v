(**

# Verified Synthesis

- verification people love soundness
- but completeness is kinda the soundness of synthesis
  - soundness I guess would be "when we return an answer, it's a valid solution"
  - completeness: if there is a solution, we will eventually find it
    (usually, if there isn't a solution, we might not terminate)

- set up basic toy language

    e ::= zero | one | var | plus e e

  the semantics of this programming language are given by

  eval : nat -> expr -> nat
  eval x zero = 0
  eval x one = 1
  eval x var = x
  eval x (plus e1 e2) = eval x e1 + eval x e2

- synthesis problem:
  - given a specification P : nat -> expr -> Prop (that satisfies some conditions to be given later)
  - find an expression such that `forall x, P x e`

- so far, P is completely arbitrary, but not all P make sense
- first, P should be *semantic*, not syntactic

    P_ext : forall x e1 e2, eval x e1 = eval x e2 -> (P x e1 <-> P x e2)

  another way to say this would be to make P : nat -> nat -> Prop and then use
  `P x (eval x e)`. this actually might be better, because it makes it clear that
  the specification specifies the *behavior* of the program, not its implementation per se.

- note that P could be nondeterministic, in that it allows multiple behaviors for a given x

- without further information about P, there's nowhere to start synthesis, so we need a few additional
  assumptions.  first, we assuem an oracle that can check whether an expression satisifies
  P on all inputs.

      P_oracle : forall e, {x : nat | ~ P x e} + {forall x, P x e}

  this either finds a counterexample x where e doesn't satisfy P.

  such an oracle immediately gives a semidecision procedure: just enumerate all expressions
  and pass them to the oracle. if there is a solution, this strategy is guaranteed to find it.
  (if there's no solution, it will just go on forever enumerating all expressions and checking them.)

  this strategy is sound (an expression returned is guaranteed to be a valid solution) because
  it only returns expressions that the oracle says are good, and we are assuming the oracle is sound.
  the strategy is also complete, because if there is a solution, it will eventually be reached by the
  enumeration, at which point the oracle will say yes.

  we can improve on this strategy in two ways. first, whenever the oracle says "no", we'll remember
  the counterexample x, so that we can check our future guesses and not make the same mistake again.
  to do so, we need to assume that `P` is checkable at each input

      P_dec : forall x e, {P x e} + {~ P x e}

  using `P_dec`, we can check our guesses against all counterexamples the oracle has ever given us.
  generally, we expect checking a guess against all such counterexamples to be faster than calling
  the oracle (in practice, `P_dec` amounts to a call to `eval`, while `P_oracle` typically involves
  an SMT solver).

  the final trick in syntactic enumerative CEGIS in to use the list of counterexamples to prune
  the enumeration. since we're checking all our guesses against the list of counterexamples,
  we're only really interested in finding the smallest expression which satisfies `P` on all the inputs
  we've seen so far.
  thus, it suffices to consider expressions equivalent if their behavior agrees on all these inputs.
  this can *vastly* cut down on the search space. for example, in our toy language there are
  21612 syntactically distinct expressions of height <= 4, but only 45 of them are semantically distinct.

  CEGIS enumerates semantically distinct expressions by iteratively deepening a set of
  known-distinct expressions. at each step, it explores all expressions whose children
  are in the known set, and adds any semantically new expressions to the set.

- now, completeness gets a little bit interesting, because *not every expression is passed to the oracle*

- high level strategy: Syntactic enumerative CEGIS [Sketch 06, Transit 13, Sygus 13]
  - enumerate all expressions in order of increasing height, and check each one



*)

Require Import List Omega Relations ExtensionalMaps RelationClasses DecidableClass EquivDec TotalOrder.
Import ListNotations.

Section list_lemmas.
  Lemma skipn_length :
    forall A n (l : list A),
      List.length l <= n ->
      skipn n l = [].
  Proof.
    induction n; destruct l; simpl; intros LE; try omega; auto with *.
  Qed.

  Lemma map_eq_Forall_eq :
    forall A B (f g : A -> B) l,
      map f l = map g l ->
      Forall (fun x => f x = g x) l.
  Proof.
    induction l; simpl; intros ME; inversion ME; subst; clear ME; constructor; auto.
  Qed.

  Lemma Forall_True:
    forall A (l : list A), Forall (fun _ => True) l.
  Proof.
    induction l; constructor; auto.
  Qed.

  Lemma Forall_app :
    forall A (P : A -> Prop) l1 l2,
      Forall P l1 ->
      Forall P l2 ->
      Forall P (l1 ++ l2).
  Proof.
    induction 1; intros F2; simpl.
    - assumption.
    - constructor; auto.
  Qed.

  Lemma Forall_flatmap :
    forall A B (f : A -> list B) (P : B -> Prop) l,
      Forall (fun a => Forall P (f a)) l ->
      Forall P (flat_map f l).
  Proof.
    induction 1; simpl.
    - constructor.
    - apply Forall_app; auto.
  Qed.

  Lemma Forall_map :
    forall A B (f : A -> B) (P : B -> Prop) l,
      Forall (fun a => P (f a)) l ->
      Forall P (map f l).
  Proof.
    induction 1; simpl; constructor; auto.
  Qed.

  Lemma fold_left_ind :
    forall A B (P : A -> Prop) (Q : B -> Prop) (f : A -> B -> A) l z,
      (forall a b, P a -> Q b -> P (f a b)) ->
      Forall Q l ->
      P z ->
      P (fold_left f l z).
  Proof.
    intros A B P Q f.
    induction l; intros z Pf F Pz; cbn [fold_left].
    - assumption.
    - inversion F; subst; clear F.
      eauto.
  Qed.

  Lemma filter_length_monotonic :
    forall A (f g : A -> bool),
      (forall x, f x = true -> g x = true) ->
      forall l,
        length (filter f l) <= length (filter g l).
  Proof.
    intros A f g FG.
    induction l; simpl; auto.
    destruct f eqn:EQ.
    - rewrite FG by assumption.
      simpl.
      omega.
    - destruct g; simpl; omega.
  Qed.

  Lemma filter_length_monotonic_lt :
    forall A (f g : A -> bool) x,
      (forall x, f x = true -> g x = true) ->
      f x = false ->
      g x = true ->
      forall l,
        In x l ->
        length (filter f l) < length (filter g l).
  Proof.
    intros A f g x FG Fx Gx.
    induction l; intros I; simpl in *; [now intuition| destruct I as [|I]].
    - subst.
      rewrite Fx, Gx.
      simpl.
      pose proof filter_length_monotonic _ _ _ FG l.
      omega.
    - specialize (IHl I).
      destruct (f a) eqn:EQ.
      + rewrite FG by assumption.
        simpl.
        omega.
      + destruct (g a); simpl; omega.
  Qed.
End list_lemmas.

Section Ltl_instances.
  Context (A : Set) R `(SO_R : StrictOrder A R).

  Global Instance Ltl_StrictOrder : StrictOrder (Ltl A R).
  constructor.
  - red.
    intro.
    intro.
    induction x; inversion H; subst.
    eapply StrictOrder_Irreflexive; eauto.
    eauto.
  - intros x y z XY YZ.
    generalize dependent z.
    induction XY; intros z YZ.
    + inversion YZ; subst; constructor.
    + inversion YZ; subst.
      * econstructor; eauto using StrictOrder_Transitive.
      * econstructor; eauto.
    + inversion YZ; subst.
      * econstructor; eauto.
      * eauto using Lt_tl.
  Qed.

  Context (R_dec : forall x y, Decidable (R x y))
          (EDK : EqDec A eq).

  Global Instance Ltl_Decidable : forall x y, Decidable (Ltl A R x y).
  induction x; destruct y.
  - apply Build_Decidable with (Decidable_witness := false).
    split; intro H; inversion H.
  - apply Build_Decidable with (Decidable_witness := true).
    split; auto.
    intro H; clear H.
    constructor.
  - apply Build_Decidable with (Decidable_witness := false).
    split; intro H; inversion H.
  - destruct (R_dec a a0) as [[|] HR].
    + apply Build_Decidable with (Decidable_witness := true).
      split; auto.
      intro H; clear H.
      constructor; intuition.
    + destruct (EDK a a0).
      * compute in e. subst a0.
        destruct (IHx y) as [[|] HLtl].
        -- apply Build_Decidable with (Decidable_witness := true).
           split; auto.
           intro H; clear H.
           apply Lt_tl.
           intuition.
        -- apply Build_Decidable with (Decidable_witness := false).
           split; intro H; inversion H; subst; intuition.
      * compute in c.
        apply Build_Decidable with (Decidable_witness := false).
        split; intro H; inversion H; subst; intuition.
  Defined.

  Global Instance Inhabited_list : Inhabited (list A).
  constructor.
  exact nil.
  Defined.

  Context (R_TO : TotalOrder R).

  Hint Constructors Ltl.

  Global Instance Ltl_TotalOrder : TotalOrder (Ltl A R).
  constructor.
  apply Ltl_StrictOrder.
  induction x; destruct y as [|b y]; auto.
  destruct (TotalOrder_trichotomy a b) as [|[|]]; auto.
  destruct (IHx y) as [|[|]]; subst; auto.
  Qed.

  Context (I_A : Inhabited A)
          (UO_A : UnboundedOrder R).

  Definition list_bigger (l : list A) : list A :=
    match l with
    | [] => [Inhabited_witness]
    | x :: xs => UnboundedOrder_bigger x :: xs
    end.

  Lemma list_bigger_ok :
    forall l,
      Ltl A R l (list_bigger l).
  Proof.
    destruct l; simpl.
    - constructor.
    - constructor.
      apply UnboundedOrder_bigger_ok.
  Qed.

  Global Instance Ltl_UnboundedOrder : UnboundedOrder (Ltl A R).
  apply Build_UnboundedOrder with (UnboundedOrder_bigger := list_bigger).
  exact list_bigger_ok.
  Defined.
End Ltl_instances.

(* Definition natlist_map : map.class (list nat) :=
  sortedmap.sortedmap (lt := Ltl _ lt) _ _ _ _ _ _. *)

Module env.
  Definition t V := @sortedmap.t _ (Ltl _ lt) V.

  Definition empty {V} : t V := @sortedmap.empty _ _ _.

  Definition get {V} k (m : t V) : option V :=
    sortedmap.get _ _ k m.

  Definition set {V} k v (m : t V) : t V :=
    sortedmap.set _ _ _ k v m.

  Definition keys {V} (m : t V) : list (list nat) :=
    sortedmap.keys m.

  Definition values {V} (m : t V) : list V :=
    sortedmap.values m.

  Lemma ge : forall V k, get k (@empty V) = None.
  Proof.
    intros.
    unfold get, empty.
    now rewrite sortedmap.ge.
  Qed.

  Lemma gss : forall V k (v : V) m, get k (set k v m) = Some v.
  Proof.
    unfold get, set.
    intros.
    now rewrite sortedmap.gss by eauto with typeclass_instances.
  Qed.

  Lemma gso : forall V k1 k2 (v : V) m, k1 <> k2 -> get k2 (set k1 v m) = get k2 m.
  Proof.
    unfold get, set.
    intros.
    now rewrite sortedmap.gso by eauto with typeclass_instances.
  Qed.

  Lemma keys_empty :
    forall V,
      keys (@empty V) = [].
  Proof.
    unfold keys, empty.
    apply sortedmap.keys_empty.
  Qed.

  Lemma in_keys_intro :
    forall V k v (m : t V),
      get k m = Some v ->
      In k (keys m).
  Proof.
    unfold get, keys.
    intros V k v m Get.
    eauto using sortedmap.in_keys_intro with typeclass_instances.
  Qed.

  Lemma in_keys_elim :
    forall V k (m : t V),
      In k (keys m) ->
      exists v,
        get k m = Some v.
  Proof.
    unfold get, keys.
    eauto using sortedmap.in_keys_elim with typeclass_instances.
  Qed.

  Lemma in_values_intro :
    forall V k (v : V) (m : t V),
      get k m = Some v ->
      In v (values m).
  Proof.
    unfold get, values.
    eauto using sortedmap.in_values_intro.
  Qed.

  Lemma in_values_elim :
    forall V (v : V) (m : t V),
      In v (values m) ->
      exists k, get k m = Some v.
  Proof.
    unfold get, values.
    intros V v m I.
    apply sortedmap.in_values_elim.
    eauto with typeclass_instances.
    assumption.
  Qed.
End env.

Module expr.

Inductive t :=
| zero
| one
| var
| plus : t -> t -> t
.

Fixpoint height (e : t) : nat :=
  match e with
  | zero => 1
  | one => 1
  | var => 1
  | plus e1 e2 => 1 + max (height e1) (height e2)
  end.

Lemma height_nonzero :
  forall e,
    1 <= height e.
Proof.
  destruct e; simpl; omega.
Qed.

Fixpoint eval (the_var : nat) (e : t) : nat :=
  match e with
  | zero => 0
  | one => 1
  | var => the_var
  | plus e1 e2 => eval the_var e1 + eval the_var e2
  end.

Definition sem_eq (e1 e2 : t) : Prop :=
  (forall a, eval a e1 = eval a e2).

Fixpoint all_up_to_height (n : nat) : list t :=
  match n with
  | 0 => []
  | S n =>
    zero :: one :: var ::
         let l := all_up_to_height n in
         flat_map (fun a => map (plus a) l) l
  end.

Lemma all_up_to_height_sanity :
  forall n e,
    In e (all_up_to_height n) ->
    height e <= n.
Proof.
  induction n; simpl; intros e; [now intuition|].
  intros [?|[?|[?|I]]]; subst; simpl; auto with *.
  rewrite in_flat_map in I.
  destruct I as [l [Il I]].
  rewrite in_map_iff in I.
  destruct I as [r [E Ir]].
  subst e.
  simpl.
  apply IHn in Il.
  apply IHn in Ir.
  zify. omega.
Qed.

Fixpoint all_of_exactly_height (n : nat) : list t :=
  match n with
  | 0 => []
  | 1 => [zero; one; var]
  | S n =>
    (* takes advantage of commutativity of plus *)
    flat_map (fun a => map (plus a) (all_of_exactly_height n)) (all_up_to_height n)
  end.

Lemma all_of_exactly_height_sanity :
  forall n e,
    In e (all_of_exactly_height n) ->
    height e = n.
Proof.
  induction n; simpl; intros e I; intuition.
  destruct n.
  - destruct I as [|[|[|[]]]]; subst; reflexivity.
  - rewrite in_flat_map in I.
    destruct I as [l [Il I]].
    rewrite in_map_iff in I.
    destruct I as [r [E Ir]].
    subst e.
    simpl.
    apply all_up_to_height_sanity in Il.
    apply IHn in Ir.
    zify. omega.
Qed.

Lemma all_up_to_height_complete :
  forall e n,
    height e <= n ->
    In e (all_up_to_height n).
Proof.
  induction e; simpl; destruct n; intros; try omega; simpl; intuition.
  do 3 right.
  rewrite in_flat_map.
  exists e1.
  split.
  - apply IHe1.
    zify. omega.
  - apply in_map.
    apply IHe2.
    zify. omega.
Qed.

Lemma sem_eq_refl :
  forall e,
    sem_eq e e.
Proof.
  intros.
  red.
  auto.
Qed.

Lemma sem_eq_plus_cong :
  forall e1 e1' e2 e2',
    sem_eq e1 e1' ->
    sem_eq e2 e2' ->
    sem_eq (plus e1 e2) (plus e1' e2').
Proof.
  unfold sem_eq.
  simpl.
  intros e1 e1' e2 e2' H1 H2 a.
  now rewrite H1, H2.
Qed.

Lemma sem_eq_plus_comm :
  forall e1 e2,
    sem_eq (plus e1 e2) (plus e2 e1).
Proof.
  unfold sem_eq.
  simpl.
  intros.
  omega.
Qed.

Lemma sem_eq_trans :
  forall a b c,
    sem_eq a b ->
    sem_eq b c ->
    sem_eq a c.
Proof.
  unfold sem_eq.
  intros a b c AB BC x.
  now rewrite AB, BC.
Qed.

Lemma all_of_exactly_height_complete :
  forall e n,
    height e = n ->
    exists e',
      In e' (all_of_exactly_height n) /\
      sem_eq e e'.
Proof.
  induction e; simpl; intros n H; subst n.
  - simpl. eauto using sem_eq_refl.
  - simpl. eauto using sem_eq_refl.
  - simpl. eauto 7 using sem_eq_refl.
  - cbn [all_of_exactly_height].
    apply Max.max_case_strong with (n := height e1) (m := height e2); intro LE;
      match goal with
      | [ _ : _ <= height ?e |- _ ] =>
        assert (1 <= height e) by (destruct e; simpl; omega);
        destruct (height e) eqn:?; [simpl; omega|];
        match goal with
        | [ IH : context [e] |- _ ] =>
          specialize (IH _ eq_refl);
          destruct IH as [e' [I SE]]
        end;
        match goal with
        | [ H: context [height ?e2] |- _ ] =>
          pose proof (all_up_to_height_complete e2 (S n) ltac:(assumption))
        end;
        eexists;
        split;
        [ rewrite in_flat_map;
          eexists; (split; [eassumption|]);
          rewrite in_map_iff;
          eexists; split; [reflexivity|eassumption]
        | now eauto using sem_eq_trans, sem_eq_plus_comm, sem_eq_plus_cong, sem_eq_refl
        ]
      end.
Qed.

Definition key (l : list nat) (e : t) : list nat :=
  List.map (fun a => eval a e) l.

Definition add_to_env_mod (l : list nat) (E : env.t t) (e : t) : list (list nat) * env.t t :=
  let k := key l e in
  match env.get k E with
  | None => ([k], env.set k e E)
  | Some _ => ([], E)
  end.

Definition add_all_to_env_mod (l : list nat) (ks : list (list nat)) (E : env.t t) (es : list t) : list (list nat) * env.t t :=
  List.fold_left (fun '(l1, E) e => let '(l2, E) := add_to_env_mod l E e in (l2 ++ l1, E)) es
                 (ks, E).

Definition height_one_mod (l : list nat) : list (list nat) * env.t t :=
  add_all_to_env_mod l [] env.empty [zero; one; var].

Definition deepen_height_mod (l : list nat) (E : env.t t) : list (list nat) * env.t t :=
  add_all_to_env_mod l [] E
                     (let es := env.values E in
                      flat_map (fun a => map (plus a) es) es).

Definition all_up_to_height_mod (l : list nat) : nat -> env.t t :=
  fix go h :=
    match h with
    | 0 => env.empty
    | 1 => let '(ks, E) := height_one_mod l in
          E
    | S h => let '(ks, E) := deepen_height_mod l (go h) in
            E
    end.

Definition eq_mod (l : list nat) (e1 e2 : t) : Prop :=
  key l e1 = key l e2.

Lemma sem_eq_eq_mod :
  forall e1 e2,
    sem_eq e1 e2 ->
    forall l, eq_mod l e1 e2.
Proof.
  intros e1 e2 SE l.
  unfold eq_mod, key, sem_eq in *.
  now apply map_ext.
Qed.

Lemma get_add_to_env_mod :
  forall os l E e e' ks E',
    add_to_env_mod l E e = (ks, E') ->
    env.get os E' = Some e' ->
    e = e' \/ env.get os E = Some e'.
Proof.
  unfold add_to_env_mod.
  intros os l E e e' ks E' Add Get.
  destruct (env.get _ E) eqn:EQ; invc Add.
  - auto.
  - destruct (list_eq_dec eq_nat_dec os (key l e)).
    + subst os.
      rewrite env.gss in Get.
      left. congruence.
    + rewrite env.gso in Get by congruence.
      auto.
Qed.

Lemma add_all_to_env_sanity :
  forall n l es ks E,
    (forall os e, env.get os E = Some e -> height e <= n) ->
    Forall (fun e => height e <= n) es ->

    forall ks' E' os e,
      add_all_to_env_mod l ks E es = (ks', E') ->
      env.get os E' = Some e ->
      height e <= n.
Proof.
  unfold add_all_to_env_mod.
  intros n l es ks E GetE F.
  apply fold_left_ind with (Q := (fun e => height e <= n)); auto.
  - clear es ks E GetE F.
    intros [ks E] e GetE He ks' E' os e1 Add1 Get1.
    destruct add_to_env_mod eqn:EQ. invc Add1.
    eapply get_add_to_env_mod in Get1; try apply EQ.
    destruct Get1; subst; eauto.
  - intros ks' E' os e EQ Get.
    invc EQ.
    eauto.
Qed.

Lemma add_to_env_mod_sound :
  forall l E e os,
    (forall e, env.get os E = Some e -> key l e = os) ->
    forall ks E' e',
      add_to_env_mod l E e = (ks, E') ->
      env.get os E' = Some e' ->
      key l e' = os.
Proof.
  unfold add_to_env_mod in *.
  intros l E e os GetE ks E' e1 Add Get1.
  destruct (env.get (key _ _) E) eqn:EQ; invc Add; [now auto|].
  destruct (list_eq_dec eq_nat_dec os (key l e)).
  - subst os. rewrite env.gss in Get1.
    inversion Get1. subst. reflexivity.
  - rewrite env.gso in Get1 by congruence.
    eauto.
Qed.

Lemma add_all_to_env_sound :
  forall l es ks E,
    (forall os e, env.get os E = Some e -> key l e = os) ->
    forall os ks' E' e,
      add_all_to_env_mod l ks E es = (ks', E') ->
      env.get os E' = Some e ->
      key l e = os.
Proof.
  unfold add_all_to_env_mod.
  intros l es ks E GetE os.
  apply fold_left_ind with (Q := fun _ => True); auto.
  - clear es E GetE.
    intros [ks1 E1] e GetE _ ks2 E2 e1 Add Get1.
    destruct add_to_env_mod eqn:EQ. invc Add.
    eapply add_to_env_mod_sound; eauto.
  - apply Forall_True.
  - intros ks' E' e EQ Get.
    invc EQ.
    auto.
Qed.

Lemma add_to_env_mod_pass_through :
  forall l E e k1 e1 ks' E',
    env.get k1 E = Some e1 ->
    add_to_env_mod l E e = (ks', E') ->
    env.get k1 E' = Some e1.
Proof.
  unfold add_to_env_mod.
  intros l E e k1 e1 ks' E' Get Add.
  destruct (env.get (key l e) E) eqn:EQ; invc Add; [now auto|].
  rewrite env.gso; [now auto|].
  intro C. subst k1.
  congruence.
Qed.

Lemma get_add_all_to_env :
  forall l es ks E k e ks' E',
    add_all_to_env_mod l ks E es = (ks', E') ->
    env.get k E = Some e ->
    env.get k E' = Some e.
Proof.
  unfold add_all_to_env_mod.
  intros l es ks E k e ks1 E1 Add Get.
  revert ks1 E1 Add.
  apply fold_left_ind with (Q := fun _ => True); auto using Forall_True.
  - clear ks E Get.
    intros [ks E] e' Get _ ks1 E1 Add.
    destruct add_to_env_mod eqn:EQ.
    invc Add.
    eauto using add_to_env_mod_pass_through.
  - intros ks1 E1 EQ.
    now invc EQ.
Qed.

Lemma eq_mod_refl :
  forall l e,
    eq_mod l e e.
Proof.
  now unfold eq_mod.
Qed.

Lemma eq_mod_trans :
  forall l e1 e2 e3,
    eq_mod l e1 e2 ->
    eq_mod l e2 e3 ->
    eq_mod l e1 e3.
Proof.
  unfold eq_mod.
  intros.
  congruence.
Qed.

Lemma eq_mod_plus_cong :
  forall l e1 e1' e2 e2',
    eq_mod l e1 e1' ->
    eq_mod l e2 e2' ->
    eq_mod l (plus e1 e2) (plus e1' e2').
Proof.
  unfold eq_mod, key.
  intros l e1 e1' e2 e2' E1 E2.
  simpl.
  apply map_eq_Forall_eq in E1.
  rewrite Forall_forall in E1.
  apply map_eq_Forall_eq in E2.
  rewrite Forall_forall in E2.
  apply map_ext_in.
  intros x I.
  now rewrite E1, E2 by assumption.
Qed.

Lemma add_to_env_mod_complete :
  forall l e E ks E',
    (forall k1 e1, env.get k1 E = Some e1 -> key l e1 = k1) ->
    add_to_env_mod l E e = (ks, E') ->
    exists e',
      eq_mod l e e' /\
      env.get (key l e) E' = Some e'.
Proof.
  intros l e E ks E' Sound.
  unfold add_to_env_mod.
  intro Add.
  destruct (env.get _ E) eqn:EQ; invc Add.
  - rewrite EQ.
    eexists.
    split; [|reflexivity].
    unfold eq_mod.
    now apply Sound in EQ.
  - rewrite env.gss.
    eauto using eq_mod_refl.
Qed.

Lemma eq_mod_key :
  forall l e1 e2,
    eq_mod l e1 e2 ->
    key l e1 = key l e2.
Proof.
  now unfold eq_mod.
Qed.

Lemma same_key_eval :
  forall e1 e2 x l,
    key l e1 = key l e2 ->
    In x l ->
    eval x e1 = eval x e2.
Proof.
  induction l; simpl; intros; intuition.
  - subst.
    inversion H; congruence.
  - inversion H; subst; clear H. auto.
Qed.


Lemma add_to_env_mod_ks' :
  forall l E e ks' E' k,
    add_to_env_mod l E e = (ks', E') ->
    In k ks' ->
    exists e,
      env.get k E' = Some e.
Proof.
  unfold add_to_env_mod.
  intros l E e ks' E' k Add I.
  destruct env.get eqn:EQ; invc Add; simpl in I; intuition.
  subst k.
  rewrite env.gss.
  eauto.
Qed.

Lemma add_all_to_env_ks' :
  forall l ks E es ks' E' k,
    (forall k, In k ks -> exists e, env.get k E = Some e) ->
    add_all_to_env_mod l ks E es = (ks', E') ->
    In k ks' ->
    exists e,
      env.get k E' = Some e.
Proof.
  unfold add_all_to_env_mod.
  intros l ks E es ks' E' k HE.
  revert ks' E'.
  apply fold_left_ind with (Q := fun _ => True).
  - intros [ks1 E1] e1 IH _ ks' E'.
    destruct add_to_env_mod eqn:EQ.
    intros H I.
    invc H.
    apply in_app_or in I as [I|I].
    + eauto using add_to_env_mod_ks'.
    + specialize (IH _ _ eq_refl I) as [e Get].
      eauto using add_to_env_mod_pass_through.
  - auto using Forall_True.
  - intros ks' E' EQ I.
    invc EQ.
    auto.
Qed.

Lemma add_all_to_env_mod_in_ks_pass_through :
  forall l es ks E ks' E' k,
    add_all_to_env_mod l ks E es = (ks', E') ->
    In k ks ->
    In k ks'.
Proof.
  unfold add_all_to_env_mod.
  intros l es ks E.
  apply fold_left_ind with (Q := fun _ => True).
  - clear es.
    intros [ks1 E1] e IH _ ks' E' k.
    destruct add_to_env_mod eqn:EQ.
    intros H; invc H.
    intros I.
    eauto using in_or_app.
  - auto using Forall_True.
  - intros ks' E' k EQ.
    invc EQ.
    auto.
Qed.

Lemma add_to_env_mod_e_key :
  forall l E e ks' E',
    add_to_env_mod l E e = (ks', E') ->
    In (key l e) ks' \/ In (key l e) (env.keys E).
Proof.
  unfold add_to_env_mod.
  intros l E e ks' E' Add.
  destruct env.get eqn:EQ; invc Add.
  - eauto using env.in_keys_intro.
  - intuition.
Qed.

Lemma add_all_to_env_mod_in_ks'_intro :
  forall l es ks E ks' E' e,
    add_all_to_env_mod l ks E es = (ks', E') ->
    In e es ->
    In (key l e) ks' \/ In (key l e) (env.keys E).
Proof.
  unfold add_all_to_env_mod.
  induction es; intros ks E ks' E' e Add I; simpl in *; [destruct I|destruct I as [EQ|I]];
    destruct add_to_env_mod as [ks1 E1] eqn:Add1.
  - subst a.
    apply add_to_env_mod_e_key in Add1 as [I|I]; [|now auto].
    eauto using add_all_to_env_mod_in_ks_pass_through, in_or_app.
  - specialize (IHes _ _ _ _ _ Add I) as [Ie|Ie]; [now auto|].
    unfold add_to_env_mod in Add1.
    destruct env.get eqn:EQ; invc Add1; [now auto|].
    apply env.in_keys_elim in Ie as [v Get].
    destruct (equiv_dec (key l e) (key l a)) as [EK|NK]; unfold equiv, complement in *.
    + left.
      eapply add_all_to_env_mod_in_ks_pass_through; eauto.
      simpl; auto.
    + rewrite env.gso in Get by congruence.
      right.
      eauto using env.in_keys_intro.
Qed.

Lemma add_to_env_ks_in_E_keys :
  forall l E e ks' E' k,
    add_to_env_mod l E e = (ks', E') ->
    In k ks' ->
    In k (env.keys E').
Proof.
  intros l E e ks' E' k Add I.
  eapply add_to_env_mod_ks' in Add; try apply I.
  destruct Add as [e1 Get1].
  eauto using env.in_keys_intro.
Qed.

Lemma add_to_env_mod_pass_through_E_keys :
  forall l E e k ks' E',
    In k (env.keys E) ->
    add_to_env_mod l E e = (ks', E') ->
    In k (env.keys E').
Proof.
  intros l E e k ks' E' I Add.
  apply env.in_keys_elim in I as [v Get].
  eapply add_to_env_mod_pass_through in Add; try apply Get.
  eauto using env.in_keys_intro.
Qed.

Lemma add_all_to_env_ks_in_E_keys :
  forall l es ks E ks' E' k,
    add_all_to_env_mod l ks E es = (ks', E') ->
    (forall k, In k ks -> In k (env.keys E)) ->
    In k ks' ->
    In k (env.keys E').
Proof.
  unfold add_all_to_env_mod.
  induction es; intros ks E ks' E' k Add H I; simpl in Add.
  - invc Add. auto.
  - destruct add_to_env_mod as [ks1 E1] eqn:EQ.
    apply IHes with (k := k) in Add; auto.
    intros k' I'.
    apply in_app_or in I' as [I'|I'].
    + eauto using add_to_env_ks_in_E_keys.
    + fold (add_all_to_env_mod l (ks1 ++ ks) E1 es) in Add.
      eauto using add_to_env_mod_pass_through_E_keys.
Qed.


Lemma height_one_mod_ks_in_E_keys :
  forall l ks E k,
    height_one_mod l = (ks, E) ->
    In k ks ->
    In k (env.keys E).
Proof.
  unfold height_one_mod.
  intros l ks E k HOM I.
  eauto using add_all_to_env_ks_in_E_keys.
Qed.

Lemma height_one_mod_complete_ks :
  forall l e ks E,
    height_one_mod l = (ks, E) ->
    height e <= 1 ->
    In (key l e) ks.
Proof.
  unfold height_one_mod.
  intros l e ks E HOM He.
  apply add_all_to_env_mod_in_ks'_intro with (e := e) in HOM.
  + destruct HOM as [I|I]; [now auto|].
    now rewrite env.keys_empty in I.
  + destruct e; simpl in *; auto.
    exfalso.
    specialize (height_nonzero e1).
    specialize (height_nonzero e2).
    zify. omega.
Qed.

Lemma deepen_height_mod_ks_in_E_keys :
  forall l E ks' E' k,
    deepen_height_mod l E = (ks', E') ->
    In k ks' ->
    In k (env.keys E').
Proof.
  unfold deepen_height_mod.
  intros l E ks' E' k Add I.
  eapply add_all_to_env_ks_in_E_keys; try apply Add; intuition.
Qed.

Lemma add_all_to_env_mod_pass_through_E_keys :
  forall l ks E es ks' E' k,
    add_all_to_env_mod l ks E es = (ks', E') ->
    In k (env.keys E) ->
    In k (env.keys E').
Proof.
  intros l ks E es ks' E' k Add I.
  apply env.in_keys_elim in I as [v Get].
  eapply get_add_all_to_env in Get; try apply Add.
  eauto using env.in_keys_intro.
Qed.

Lemma deepen_height_mod_pass_through :
  forall l E ks' E' k,
    deepen_height_mod l E = (ks', E') ->
    In k (env.keys E) ->
    In k (env.keys E').
Proof.
  unfold deepen_height_mod.
  eauto using add_all_to_env_mod_pass_through_E_keys.
Qed.

Lemma height_one_mod_sanity :
  forall l ks E k e,
    height_one_mod l = (ks, E) ->
    env.get k E = Some e ->
    height e <= 1.
Proof.
  unfold height_one_mod.
  intros l ks E k e Add Get.
  eapply add_all_to_env_sanity in Add; eauto.
  intros k1 e1 Get1.
  now rewrite env.ge in Get1.
Qed.

Lemma deepen_height_mod_sanity :
  forall l h E ks' E',
    (forall k e, env.get k E = Some e -> height e <= h) ->
    deepen_height_mod l E = (ks', E') ->
    forall k e,
      env.get k E' = Some e ->
      height e <= S h.
Proof.
  unfold deepen_height_mod.
  intros l h E ks' E' E_sanity Add k e Get.
  eapply add_all_to_env_sanity; try apply Add; eauto.
  apply Forall_flatmap.
  apply Forall_forall.
  intros e1 I1.
  apply env.in_values_elim in I1 as [k1 Get1].
  pose proof E_sanity _ _ Get1 as He1.
  apply Forall_map.
  apply Forall_forall.
  intros e2 I2.
  apply env.in_values_elim in I2 as [k2 Get2].
  pose proof E_sanity _ _ Get2 as He2.
  simpl. zify. omega.
Qed.

Lemma all_up_to_height_mod_sanity :
  forall l n os e,
    env.get os (all_up_to_height_mod l n) = Some e ->
    height e <= n.
Proof.
  induction n; simpl; intros k e Get.
  - now rewrite env.ge in Get.
  - destruct n.
    + destruct height_one_mod as [ks E] eqn:HOM.
      eauto using height_one_mod_sanity.
    + destruct deepen_height_mod as [ks E] eqn:Deep.
      eauto using deepen_height_mod_sanity.
Qed.

Lemma height_one_mod_sound :
  forall l k e ks' E',
    height_one_mod l = (ks', E') ->
    env.get k E' = Some e ->
    key l e = k.
Proof.
  unfold height_one_mod.
  intros l k e ks' E' Add Get.
  eapply add_all_to_env_sound; eauto.
  intros k1 e1 Get1.
  now rewrite env.ge in Get1.
Qed.

Lemma deepen_height_mod_sound :
  forall l E ks' E',
    (forall k e, env.get k E = Some e -> key l e = k) ->
    deepen_height_mod l E = (ks', E') ->
    forall k e,
      env.get k E' = Some e ->
      key l e = k.
Proof.
  unfold deepen_height_mod.
  eauto using add_all_to_env_sound.
Qed.

Lemma all_up_to_height_mod_sound :
  forall l n os e,
    env.get os (all_up_to_height_mod l n) = Some e ->
    key l e = os.
Proof.
  induction n; simpl; intros os e Get.
  - now rewrite env.ge in Get.
  - destruct n.
    + destruct height_one_mod eqn:HOM.
      eauto using height_one_mod_sound.
    + destruct deepen_height_mod as [ks E] eqn:Deep.
      eauto using deepen_height_mod_sound.
Qed.

Lemma deepen_height_mod_all_up_to_height :
  forall l h ks E,
    1 <= h ->
    deepen_height_mod l (all_up_to_height_mod l h) = (ks, E) ->
    E = all_up_to_height_mod l (S h).
Proof.
  intros l h ks E Deep.
  simpl.
  destruct h; [omega|].
  remember (S h) as h' eqn:EQ.
  clear EQ. clear h. rename h' into h.
  destruct deepen_height_mod; congruence.
Qed.

Lemma deepen_height_mod_complete' :
  forall l h E ks' E' e,
    1 <= h ->
    (forall e, height e <= h -> In (key l e) (env.keys E)) ->
    (forall k e, env.get k E = Some e -> key l e = k) ->
    height e <= S h ->
    deepen_height_mod l E = (ks', E') ->
    In (key l e) ks' \/ In (key l e) (env.keys E).
Proof.
  unfold deepen_height_mod.
  intros l h E ks' E' e LE E_complete E_sound He Add.
  invc He; [|now auto].
  match goal with
  | [ H : height _ = _ |- _ ] => rename H into He
  end.
  destruct e; try solve [simpl in *; omega].
  simpl in He. assert (height e1 <= h /\ height e2 <= h) as [He1 He2] by (invc He; zify; omega). clear He.
  pose proof E_complete e1 He1 as I1.
  apply env.in_keys_elim in I1 as [e1' Get1].
  pose proof E_sound _ _ Get1 as K1.
  pose proof E_complete e2 He2 as I2.
  apply env.in_keys_elim in I2 as [e2' Get2].
  pose proof E_sound _ _ Get2 as K2.
  assert (eq_mod l (plus e1 e2) (plus e1' e2'))
    by (apply eq_mod_plus_cong; unfold eq_mod; congruence).
  erewrite eq_mod_key by eauto.
  eapply add_all_to_env_mod_in_ks'_intro; eauto.
  rewrite in_flat_map.
  exists e1'. split; [now eauto using env.in_values_intro|].
  rewrite in_map_iff.
  eexists. split; [reflexivity|].
  now eauto using env.in_values_intro.
Qed.

Lemma all_up_to_height_mod_complete :
  forall l n e,
    height e <= n ->
    In (key l e) (env.keys (all_up_to_height_mod l n)).
Proof.
  induction n; intros e He; simpl.
  - destruct e; simpl in *; omega.
  - destruct n.
    + destruct height_one_mod as [ks E] eqn:HOM.
      eauto using height_one_mod_ks_in_E_keys, height_one_mod_complete_ks.
    + destruct deepen_height_mod as [ks E] eqn:Deep.
      remember (S n) as m in *.
      pose proof deepen_height_mod_complete' _ m _ _ _ _ ltac:(omega) ltac:(eauto) (all_up_to_height_mod_sound l m) He Deep as [I|I].
      * eauto using deepen_height_mod_ks_in_E_keys.
      * eauto using deepen_height_mod_pass_through.
Qed.

Lemma deepen_height_mod_complete :
  forall l h ks' E' e,
    1 <= h ->
    height e <= S h ->
    deepen_height_mod l (all_up_to_height_mod l h) = (ks', E') ->
    In (key l e) ks' \/ In (key l e) (env.keys (all_up_to_height_mod l h)).
Proof.
  intros l h ks' E' e He Deep.
  eauto using deepen_height_mod_complete', all_up_to_height_mod_complete, all_up_to_height_mod_sound.
Qed.

End expr.

Eval lazy in length (expr.all_up_to_height 4).
Eval lazy in length (proj1_sig (expr.all_up_to_height_mod [0; 1] 4)).


Module state.
  Record t := Make { height: nat; env: env.t expr.t; queue : list (list nat); inputs: list nat }.

  Definition init (l : list nat) : t :=
    let '(ks, E) := expr.height_one_mod l in
    Make 1 E ks l.
End state.

Section cozy.

  Variable P : nat -> expr.t -> Prop.
  Hypothesis P_ext : forall x e1 e2, expr.eval x e1 = expr.eval x e2 -> P x e1 <-> P x e2.

  Hypothesis P_dec : nat -> expr.t -> bool.
  Hypothesis P_dec_ok : forall x e, Bool.reflect (P x e) (P_dec x e).

  Hypothesis P_oracle : forall e, {x : nat | ~ P x e} + {forall x, P x e}.

  Definition check_inputs (l : list nat) (e : expr.t) : bool :=
    forallb (fun n => P_dec n e) l.

  Lemma check_inputs_ok :
    forall e l,
      if check_inputs l e
      then Forall (fun n => P n e) l
      else Exists (fun n => ~ P n e) l
  .
  Proof.
    induction l; simpl.
    - constructor.
    - destruct (P_dec_ok a e); cbn[andb].
      + destruct check_inputs; auto.
      + eauto.
  Qed.

  Definition step (s : state.t) : state.t + expr.t :=
    match s.(state.queue) with
    | [] =>
      let '(ks, E) := expr.deepen_height_mod s.(state.inputs) s.(state.env) in
      inl (state.Make (S s.(state.height))
                      E
                      ks
                      s.(state.inputs))
    | k :: q =>
      match env.get k s.(state.env) with
      | None => inl (state.Make s.(state.height) s.(state.env) q s.(state.inputs))
      | Some e =>
        if check_inputs s.(state.inputs) e
        then
          match P_oracle e with
          | inleft (exist _ x pf) => inl (state.init (x :: s.(state.inputs)))
          | inright _ => inr e
          end
        else
          inl (state.Make s.(state.height) s.(state.env) q s.(state.inputs))
      end
    end.

  Fixpoint run (n : nat) (s : state.t) : state.t + expr.t :=
    match n with
    | 0 => inl s
    | S n =>
      match step s with
      | inl s => run n s
      | inr e => inr e
      end
    end.

  Definition inv (s : state.t) : Prop :=
    (forall k, In k s.(state.queue) -> exists e, env.get k s.(state.env) = Some e) /\
    (s.(state.env) = expr.all_up_to_height_mod s.(state.inputs) s.(state.height)) /\
    (forall e,
      expr.height e <= s.(state.height) ->
      (exists x, In x s.(state.inputs) /\ ~P x e) \/ In (expr.key s.(state.inputs) e) s.(state.queue)) /\
    1 <= s.(state.height)
  .

  Lemma init_inv :
    forall l, inv (state.init l).
  Proof.
    unfold inv, state.init.
    intros l.
    destruct expr.height_one_mod as [ks E] eqn:EQ.
    simpl.
    rewrite EQ.
    intuition.
    - unfold expr.height_one_mod in *.
      eapply expr.add_all_to_env_ks'; try apply EQ; intuition.
    - eauto using expr.height_one_mod_complete_ks.
  Qed.

  Lemma step_inr :
    forall s e,
      inv s ->
      step s = inr e ->
      forall x, P x e.
  Proof.
    unfold step.
    unfold inv.
    intros s e Inv Step.
    destruct state.queue; [destruct expr.deepen_height_mod; discriminate|].
    destruct Inv as [GetQ [Env Done]].
    destruct (GetQ l ltac:(intuition)) as [e1 Get1].
    rewrite Get1 in Step.
    destruct check_inputs; [|discriminate].
    destruct P_oracle as [[]|]; [discriminate|].
    inversion Step; subst; clear Step.
    assumption.
  Qed.

  Lemma step_inl :
    forall s s',
      inv s ->
      step s = inl s' ->
      inv s'.
  Proof.
    unfold step.
    intros s s' Inv Step.
    destruct state.queue eqn:EQ.
    - destruct expr.deepen_height_mod as [ks E] eqn:Deep.
      invc Step.
      unfold inv.
      cbn [state.inputs state.height state.queue state.env] in *.
      split; [|split; [|split]].
      + unfold expr.deepen_height_mod in Deep.
        intros k I.
        eapply expr.add_all_to_env_ks'; try apply Deep; intuition.
      + destruct Inv as [_ [Inv [_ LEH]]].
        rewrite Inv in Deep.
        eauto using expr.deepen_height_mod_all_up_to_height.
      + intros e He.
        destruct Inv as [GetQ [Inv [Done LEH]]].
        unfold expr.deepen_height_mod in Deep.
        rewrite Inv in Deep.
        pose proof expr.deepen_height_mod_complete _ _ _ _ _ LEH He Deep as [I|I]; [now auto|].
        apply env.in_keys_elim in I as [v Get].
        pose proof expr.all_up_to_height_mod_sanity _ _ _ _ Get as Hv.
        specialize (Done v Hv) as [[x [I NP]]|I]; [|now rewrite EQ in I; intuition].
        pose proof expr.all_up_to_height_mod_sound _ _ _ _ Get.
        left. exists x. split; [assumption|].
        now rewrite P_ext with (e2 := v) by eauto using expr.same_key_eval.
      + omega.
    - unfold inv in Inv.
      destruct Inv as [GetQ [Env [Done LEH]]].
      destruct (GetQ l) as [e Get]; [now rewrite EQ; intuition|].
      rewrite Get in Step.
      pose proof check_inputs_ok e (state.inputs s) as CI.
      destruct check_inputs.
      + destruct P_oracle as [[x pf]|]; [|discriminate].
        inversion Step; subst; clear Step.
        apply init_inv.
      + invc Step.
        unfold inv in *.
        cbn [state.inputs state.height state.queue state.env] in *.
        split; [|split; [|split]].
        * intros k I.
          apply GetQ.
          rewrite EQ.
          intuition.
        * auto.
        * intros e1 He1.
          destruct (Done e1 He1) as [| I]; [now auto|].
          rewrite EQ in I.
          simpl in I.
          destruct I as [|I]; [|now auto].
          subst.
          rewrite Env in *.
          pose proof expr.all_up_to_height_mod_sound _ _ _ _ Get.
          apply Exists_exists in CI.
          destruct CI as [x [I NP]].
          left.
          exists x.
          rewrite P_ext. eauto.
          eauto using expr.same_key_eval.
        * assumption.
  Qed.

  Lemma run_inl :
    forall n s s',
      inv s ->
      run n s = inl s' ->
      inv s'.
  Proof.
    induction n; simpl; intros s s' Inv Run.
    - inversion Run; subst; assumption.
    - destruct step eqn:?; [|discriminate].
      eauto using step_inl.
  Qed.

  Lemma run_inr :
    forall n s e,
      inv s ->
      run n s = inr e ->
      forall x, P x e.
  Proof.
    induction n; simpl; intros s e Inv Run; [discriminate|].
    destruct step eqn:?.
    - eauto using step_inl.
    - inversion Run; subst; clear Run.
      eauto using step_inr.
  Qed.

  Lemma run_plus :
    forall n1 n2 s,
      run (n1 + n2) s =
      match run n1 s with
      | inl s => run n2 s
      | inr e => inr e
      end.
  Proof.
    induction n1; simpl; intros n2 s.
    - reflexivity.
    - destruct step; auto.
  Qed.

  Lemma run_skipn :
    forall n s,
      n <= List.length s.(state.queue) ->
      (run n s = inl (state.Make s.(state.height)
                                 s.(state.env)
                                 (skipn n s.(state.queue))
                                 s.(state.inputs))) \/
      (exists n' k e x,
          n' <= n /\
          env.get k s.(state.env) = Some e /\
          Forall (fun x => P x e) s.(state.inputs) /\
          ~ P x e /\
          run n' s = inl (state.init (x :: s.(state.inputs)))) \/
      (exists e, run n s = inr e).
  Proof.
    induction n; intros s LE.
    - left. destruct s; reflexivity.
    - set (r := run (S n) s).
      cbn [run] in *.
      unfold step in *.
      destruct state.queue eqn:EQ; [simpl in *; omega|].
      destruct env.get eqn:Get.
      + pose proof check_inputs_ok t (state.inputs s) as CI.
        destruct check_inputs eqn:EQCI.
        * destruct P_oracle as [[x Hx]|] eqn:EQO.
          -- right. left.
             exists 1, l, t, x.
             split; [|split; [|split]]; auto with *.
             simpl.
             unfold step.
             now rewrite EQ, Get, EQCI, EQO.
          -- subst r. eauto.
        * match goal with
          | [ _ := run n ?s |- _ ] =>
            specialize (IHn s ltac:(simpl in *; omega))
          end.
          subst r.
          simpl in *.
          destruct IHn as [Run|[[n' [k [e1 [x [LEn [Get1 [F [NP Run]]]]]]]]|[e0 Run]]].
          -- auto.
          -- right. left.
             exists (S n'), k, e1, x.
             split; [|split;[|split;[|split]]]; auto with *.
             simpl. unfold step.
             now rewrite EQ, Get, EQCI.
          -- eauto.
      + match goal with
        | [ _ := run n ?s |- _ ] =>
          specialize (IHn s ltac:(simpl in *; omega))
        end.
        subst r.
        simpl in *.
        destruct IHn as [Run|[[n' [k [e1 [x [LEn [Get1 [F [NP Run]]]]]]]]|[e0 Run]]].
        * auto.
        * right. left.
          exists (S n'), k, e1, x.
          split; [|split;[|split;[|split]]]; auto with *.
          simpl. unfold step.
          now rewrite EQ, Get.
        * eauto.
  Qed.

  Lemma finish_this_height :
    forall s,
      (exists n, run n s = inl (state.Make s.(state.height) s.(state.env) [] s.(state.inputs))) \/
      (exists n k e x,
          env.get k s.(state.env) = Some e /\
          Forall (fun x => P x e) s.(state.inputs) /\
          ~ P x e /\
          run n s = inl (state.init (x :: s.(state.inputs)))) \/
      (exists n e, run n s = inr e).
  Proof.
    intros s.
    destruct (run_skipn (length s.(state.queue)) s) as [Run|[[n' [k [e [x [Get [F [NP Run]]]]]]]|[e Run]]];
      [omega| | |].
    - rewrite skipn_length in Run by omega.
      eauto.
    - eauto 10.
    - eauto.
  Qed.

  Lemma all_heights :
    forall l h,
      1 <= h ->
      (exists n E ks,
          run n (state.init l) = inl (state.Make h E ks l)) \/
      (exists n e x,
          expr.height e <= h /\
          Forall (fun x => P x e) l /\
          ~ P x e /\
          run n (state.init l) = inl (state.init (x :: l))) \/
      (exists n e,
          run n (state.init l) = inr e).
  Proof.
    induction h; intros LE; [omega|destruct h].
    - clear IHh LE.
      left.
      unfold state.init.
      destruct expr.height_one_mod.
      exists 0. simpl. eauto.
    - specialize (IHh ltac:(omega))
        as [[n1 [E1 [ks1 Run1]]]|[[n1 [e1 [x [He1 [F1 [NP1 Run1]]]]]]|[n1 [e1 Run1]]]]; [|now eauto 10|now eauto].
      match goal with
      | [ H : run _ _ = inl ?s |- _ ] =>
        destruct (finish_this_height s) as [[n2 Run2]|
                                            [[n2 [k2 [e2 [x [Get2 [F2 [NP2 Run2]]]]]]]|
                                             [n2 [e2 Run2]]
                                           ]]
      end;
      cbn [state.inputs state.height state.queue state.env] in *.
      + left. exists (n1 + (n2 + 1)).
        rewrite run_plus, Run1, run_plus, Run2.
        simpl.
        unfold step.
        cbn [state.inputs state.height state.queue state.env] in *.
        destruct expr.deepen_height_mod as [ks2 E2] eqn:Deep.
        eauto.
      + right. left. exists (n1 + n2).
        exists e2, x.
        pose proof run_inl _ _ _ ltac:(apply init_inv) Run1 as Inv1.
        destruct Inv1 as [GetQ [Env Done]].
        cbn [state.inputs state.height state.queue state.env] in *. subst E1.
        split; [|split; [|split]]; auto.
        * apply expr.all_up_to_height_mod_sanity in Get2.
          omega.
        * now rewrite run_plus, Run1.
      + right. right. exists (n1 + n2), e2.
        now rewrite run_plus, Run1.
  Qed.

  Lemma finish_these_inputs :
    forall l e,
      (forall x, P x e) ->
      (exists n e' x, expr.height e' <= expr.height e /\
                 Forall (fun x => P x e') l /\
                 ~ P x e' /\
                 run n (state.init l) = inl (state.init (x :: l))) \/
      (exists n e', run n (state.init l) = inr e').
  Proof.
    intros l e F.
    destruct (all_heights l (expr.height e)) as [[n1 [E1 [ks1 Run1]]]|[[n1 [e1 [x [Get1 [F1 [NP1 Run1]]]]]]|[n1 [e1 Run1]]]];
      eauto 10 using expr.height_nonzero; [].
    match goal with
    | [ H : run _ _ = inl ?s |- _ ] =>
      destruct (finish_this_height s) as [[n2 Run2]|[[n2 [k [e2 [x [Get2 [F2 [NP2 Run2]]]]]]]|[n2 [e2 Run2]]]]
    end.
    - simpl in *.
      exfalso.
      apply run_inl in Run2; [|now eauto using run_inl, init_inv].
      rename Run2 into Inv2. clear Run1.
      destruct Inv2 as [GetQ [Env [Done LEH]]].
      cbn [state.inputs state.height state.queue state.env] in *.
      destruct (Done e ltac:(omega)) as [[]|[]].
      intuition.
    - simpl in *.
      left.
      exists (n1 + n2), e2, x.
      pose proof run_inl _ _ _ ltac:(apply init_inv) Run1 as Inv1.
      destruct Inv1 as [GetQ [Env Done]].
      cbn [state.inputs state.height state.queue state.env] in *. subst E1.
      split; [|split; [|split]]; auto.
      + eauto using expr.all_up_to_height_mod_sanity.
      + now rewrite run_plus, Run1.
    - right.
      exists (n1 + n2), e2.
      now rewrite run_plus, Run1.
  Qed.

  Lemma check_inputs_cons :
    forall e l x,
      check_inputs (x :: l) e = true ->
      check_inputs l e = true.
  Proof.
    simpl.
    intros e l x H.
    apply Bool.andb_true_iff in H.
    intuition.
  Qed.

  Lemma completeness' :
    forall e,
      (forall x, P x e) ->
      forall n l,
      List.length (List.filter (check_inputs l) (expr.all_up_to_height (expr.height e))) <= n ->
      exists n1 e1,
        run n1 (state.init l) = inr e1.
  Proof.
    intros e He.
    induction n; intros l Length.
    - exfalso.
      apply le_n_0_eq in Length.
      symmetry in Length.
      apply length_zero_iff_nil in Length.
      assert (In e (filter (check_inputs l) (expr.all_up_to_height (expr.height e)))) as I.
      {
        apply filter_In.
        split; [now apply expr.all_up_to_height_complete|].
        pose proof check_inputs_ok e l as HCI.
        destruct check_inputs; auto.
        apply Exists_exists in HCI.
        destruct HCI.
        intuition.
      }

      rewrite Length in I.
      intuition.
    - destruct (finish_these_inputs l e) as [[n1 [e1 [x [LE [F [NP Run1]]]]]]| [n1 [e1 Run1]]];
        [now auto| |now eauto using run_inr, init_inv].
      specialize (IHn (x :: l)).
      destruct IHn as [n2 [e2 Run2]].
      {
        apply lt_n_Sm_le.
        eapply lt_le_trans; [|apply Length].
        apply filter_length_monotonic_lt with (x := e1).
        - eauto using check_inputs_cons.
        - simpl; destruct (P_dec_ok x e1); simpl; intuition.
        - pose proof check_inputs_ok e1 l.
          destruct check_inputs; auto.
          rewrite Forall_forall in F.
          rewrite Exists_exists in H.
          destruct H. intuition.
        - auto using expr.all_up_to_height_complete.
      }
      exists (n1 + n2), e2.
      now rewrite run_plus, Run1, Run2.
  Qed.

  Theorem completeness :
    (exists e, forall x, P x e) ->
    exists n e,
      run n (state.init []) = inr e /\
      (forall x, P x e).
  Proof.
    intros [ewit Hwit].
    destruct (completeness' ewit Hwit _ [] (le_n _)) as [n [e Run]].
    exists n, e.
    split; eauto using run_inr, init_inv.
  Qed.
End cozy.

Print Assumptions completeness.