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
    1 <= expr.height e.
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
  (forall a, expr.eval a e1 = expr.eval a e2).

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
    expr.height e <= n.
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
    expr.height e = n.
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
  List.map (fun a => expr.eval a e) l.

Definition add_to_env_mod (l : list nat) (E : env.t t) (e : t) : env.t t :=
  let k := key l e in
  match env.get k E with
  | None => env.set k e E
  | Some _ => E
  end.

Definition add_all_to_env_mod (l : list nat) (E : env.t t) (es : list t) : env.t t :=
  List.fold_left (add_to_env_mod l) es E.

Fixpoint all_up_to_height_mod (l : list nat) (n : nat) : env.t t :=
  match n with
  | 0 => env.empty
  | S n =>
    let E := all_up_to_height_mod l n in
    add_all_to_env_mod l E
      (zero :: one :: var ::
           let es := env.values E in
           flat_map (fun a => map (plus a) es) es)
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
  forall os l E e e',
    env.get os (add_to_env_mod l E e) = Some e' ->
    e = e' \/ env.get os E = Some e'.
Proof.
  unfold add_to_env_mod.
  intros os l E e e' Get.
  destruct (env.get _ E) eqn:EQ.
  - auto.
  - destruct (list_eq_dec eq_nat_dec os (key l e)).
    + subst os.
      rewrite env.gss in Get.
      left. congruence.
    + rewrite env.gso in Get by congruence.
      auto.
Qed.

Lemma add_all_to_env_sanity :
  forall n l es E,
    (forall os e, env.get os E = Some e -> expr.height e <= n) ->
    Forall (fun e => expr.height e <= n) es ->
    forall os e,
      env.get os (add_all_to_env_mod l E es) = Some e ->
      expr.height e <= n.
Proof.
  unfold add_all_to_env_mod.
  intros n l es E GetE F.
  apply fold_left_ind with (Q := (fun e => expr.height e <= n)); auto.
  clear es E GetE F.
  intros E e GetE He os e1 Get1.
  apply get_add_to_env_mod in Get1.
  destruct Get1; subst; eauto.
Qed.

Lemma all_up_to_height_mod_sanity :
  forall l n os e,
    env.get os (all_up_to_height_mod l n) = Some e ->
    expr.height e <= n.
Proof.
  induction n; intros os e Get;
    [now rewrite env.ge in Get|].
  cbn [all_up_to_height_mod] in *.
  eapply add_all_to_env_sanity; try apply Get.
  - eauto.
  - clear os e Get.
    do 3 (constructor; [simpl; omega|]).
    apply Forall_flatmap.
    apply Forall_forall.
    intros e1 I1.
    apply Forall_map.
    apply Forall_forall.
    intros e2 I2.
    apply env.in_values_elim in I1.
    destruct I1 as [k1 Get1].
    apply env.in_values_elim in I2.
    destruct I2 as [k2 Get2].
    apply IHn in Get1.
    apply IHn in Get2.
    simpl. zify. omega.
Qed.

Lemma add_to_env_mod_sound :
  forall l E e os,
    (forall e, env.get os E = Some e -> key l e = os) ->
    forall e',
      env.get os (add_to_env_mod l E e) = Some e' ->
      key l e' = os.
Proof.
  unfold add_to_env_mod in *.
  intros l E e os GetE e1 Get1.
  destruct (env.get (key _ _) E) eqn:EQ; [now auto|].
  destruct (list_eq_dec eq_nat_dec os (key l e)).
  - subst os. rewrite env.gss in Get1.
    inversion Get1. subst. reflexivity.
  - rewrite env.gso in Get1 by congruence.
    eauto.
Qed.

Lemma add_all_to_env_sound :
  forall l es E,
    (forall os e, env.get os E = Some e -> key l e = os) ->
    forall os e,
      env.get os (add_all_to_env_mod l E es) = Some e ->
      key l e = os.
Proof.
  unfold add_all_to_env_mod.
  intros l es E GetE os.
  apply fold_left_ind with (Q := fun _ => True); auto.
  - clear es E GetE.
    intros E e GetE _ e1 Get1.
    eapply add_to_env_mod_sound; eauto.
  - apply Forall_True.
Qed.

Lemma all_up_to_height_mod_sound :
  forall l n os e,
    env.get os (all_up_to_height_mod l n) = Some e ->
    key l e = os.
Proof.
  induction n; intros os e Get;
    [now rewrite env.ge in Get|].
  cbn [all_up_to_height_mod] in *.
  eapply add_all_to_env_sound in Get; try apply Get.
  clear os e Get.
  intros os e Get.
  auto.
Qed.

Lemma get_add_all_to_env :
  forall l es E k e,
    env.get k E = Some e ->
    env.get k (add_all_to_env_mod l E es) = Some e.
Proof.
  unfold add_all_to_env_mod.
  intros l es E k e Get.
  apply fold_left_ind with (Q := fun _ => True); auto using Forall_True.
  clear E Get.
  intros E e' Get _.
  unfold add_to_env_mod.
  destruct (env.get (key _ _) _) eqn:EQ; [now auto|].
  now rewrite env.gso by congruence.
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
  forall l e E,
    (forall k1 e1, env.get k1 E = Some e1 -> key l e1 = k1) ->
    exists e',
      eq_mod l e e' /\
      env.get (key l e) (add_to_env_mod l E e) = Some e'.
Proof.
  intros l e E Sound.
  unfold add_to_env_mod.
  destruct (env.get _ E) eqn:EQ.
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

Lemma add_all_to_env_complete :
  forall l es E e e',
    (forall k1 e1, env.get k1 E = Some e1 -> key l e1 = k1) ->
    eq_mod l e e' ->
    In e' es ->
    exists e',
      eq_mod l e e' /\
      env.get (key l e) (add_all_to_env_mod l E es) = Some e'.
Proof.
  unfold add_all_to_env_mod.
  intros l.
  induction es; intros E e e' Sound EM I; [now intuition| destruct I as [EQ|I]];
    cbn[fold_left].
  - subst a.
    pose proof add_to_env_mod_complete l e' E as H;
      match type of H with
      | ?P -> _ => assert P as HP by assumption; specialize (H HP); clear HP
      end.
    destruct H as [e1 [EM1 Get1]].
    fold (add_all_to_env_mod l (add_to_env_mod l E e') es).
    rewrite get_add_all_to_env with (e := e1); [now eauto using eq_mod_trans|].
    erewrite eq_mod_key; eauto.
  - eauto using add_to_env_mod_sound.
Qed.

Lemma all_up_to_height_mod_complete :
  forall l n e,
    expr.height e <= n ->
    exists e',
      eq_mod l e e' /\
      env.get (key l e) (all_up_to_height_mod l n) = Some e'.
Proof.
  induction n; intros e He;
    [destruct e; simpl in *; omega|].
  cbn [all_up_to_height_mod].
  destruct e.
  - apply add_all_to_env_complete with (e' := zero).
    + now apply all_up_to_height_mod_sound.
    + auto using eq_mod_refl.
    + simpl; intuition.
  - apply add_all_to_env_complete with (e' := one).
    + now apply all_up_to_height_mod_sound.
    + auto using eq_mod_refl.
    + simpl; intuition.
  - apply add_all_to_env_complete with (e' := var).
    + now apply all_up_to_height_mod_sound.
    + auto using eq_mod_refl.
    + simpl; intuition.
  - simpl in He.
    destruct (IHn e1 (ltac:(zify; omega))) as [e1' [EM1 Get1]].
    destruct (IHn e2 (ltac:(zify; omega))) as [e2' [EM2 Get2]].
    apply add_all_to_env_complete with (e' := plus e1' e2').
    + now apply all_up_to_height_mod_sound.
    + now auto using eq_mod_plus_cong.
    + simpl.
      do 3 right.
      rewrite in_flat_map.
      apply env.in_values_intro in Get1.
      apply env.in_values_intro in Get2.
      exists e1'.
      split; [assumption|].
      rewrite in_map_iff.
      eauto.
Qed.

Lemma same_key_eval :
  forall e1 e2 x l,
    expr.key l e1 = expr.key l e2 ->
    In x l ->
    expr.eval x e1 = expr.eval x e2.
Proof.
  induction l; simpl; intros; intuition.
  - subst.
    inversion H; congruence.
  - inversion H; subst; clear H. auto.
Qed.
End expr.

Module state.
  Record t := Make { height: nat; env: env.t expr.t; queue : list (list nat); inputs: list nat }.

  Definition init (l : list nat) : t :=
    Make 0 env.empty [] l.
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
      let E := expr.all_up_to_height_mod s.(state.inputs) (S s.(state.height)) in
      inl (state.Make (S s.(state.height))
                      E
                      (env.keys E)
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
    (s.(state.height) > 0 -> s.(state.env) = expr.all_up_to_height_mod s.(state.inputs) s.(state.height)) /\
    (forall e,
      expr.height e <= s.(state.height) ->
      (exists x, ~P x e) \/ In (expr.key s.(state.inputs) e) s.(state.queue))
  .

  Lemma init_inv :
    forall l, inv (state.init l).
  Proof.
    unfold inv, state.init.
    simpl.
    intuition.
    exfalso.
    destruct e; simpl in *; omega.
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
    destruct state.queue; [discriminate|].
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
    - match goal with
      | [ H : inl ?x = inl ?y |- _ ] =>
        assert (x = y) by (now inversion H); clear H; subst
      end.
      unfold inv.
      split; [|split].
      + auto using env.in_keys_elim.
      + auto.
      + cbn [state.inputs state.height state.queue].
        intros e He.
        right.
        destruct (expr.all_up_to_height_mod_complete s.(state.inputs) (S s.(state.height)) e ltac:(assumption))
          as [e' [EM Get]].
        eauto using env.in_keys_intro.
    - unfold inv in Inv.
      destruct Inv as [GetQ [Env Done]].
      destruct (GetQ l) as [e Get]; [now rewrite EQ; intuition|].
      rewrite Get in Step.
      pose proof check_inputs_ok e (state.inputs s) as CI.
      destruct check_inputs.
      + destruct P_oracle as [[x pf]|]; [|discriminate].
        inversion Step; subst; clear Step.
        apply init_inv.
      + inversion Step; subst; clear Step.
        unfold inv in *.
        simpl.
        split; [|split].
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
          assert (state.height s > 0) as He1nz by (pose proof expr.height_nonzero e1; omega).
          specialize (Env He1nz); clear He1nz.
          rewrite Env in *.
          pose proof expr.all_up_to_height_mod_sound _ _ _ _ Get.
          apply Exists_exists in CI.
          destruct CI as [x [I NP]].
          left.
          exists x.
          rewrite P_ext. eauto.
          eauto using expr.same_key_eval.
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
      (exists n,
          run n (state.init l) = inl (state.Make h (expr.all_up_to_height_mod l h)
                                                 (env.keys (expr.all_up_to_height_mod l h)) l)) \/
      (exists n e x,
          expr.height e <= h /\
          Forall (fun x => P x e) l /\
          ~ P x e /\
          run n (state.init l) = inl (state.init (x :: l))) \/
      (exists n e,
          run n (state.init l) = inr e).
  Proof.
    induction h; [|destruct IHh as [[n1 Run1]|[[n1 [e1 [x [He1 [F1 [NP1 Run1]]]]]]|[n1 [e1 Run1]]]]]; eauto 10.
    - left. exists 0. reflexivity.
    - match goal with
      | [ H : run _ _ = inl ?s |- _ ] =>
        destruct (finish_this_height s) as [[n2 Run2]|
                                            [[n2 [k2 [e2 [x [Get2 [F2 [NP2 Run2]]]]]]]|
                                             [n2 [e2 Run2]]
                                           ]]
      end.
      cbn [state.inputs state.height state.queue state.env] in *.
      + left. exists (n1 + (n2 + 1)).
        rewrite run_plus, Run1, run_plus, Run2.
        reflexivity.
      + right. left. exists (n1 + n2).
        cbn [state.inputs state.height state.queue state.env] in *.
        exists e2, x.
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
    destruct (all_heights l (expr.height e)) as [[n1 Run1]|[[n1 [e1 [x [He1 [F1 [NP1 Run1]]]]]]|[n1 [e1 Run1]]]];
      eauto 10.
    match goal with
    | [ H : run _ _ = inl ?s |- _ ] =>
      destruct (finish_this_height s) as [[n2 Run2]|[[n2 [k [e2 [x [Get2 [F2 [NP2 Run2]]]]]]]|[n2 [e2 Run2]]]]
    end.
    - simpl in *.
      exfalso.
      apply run_inl in Run2; [|now eauto using run_inl, init_inv].
      rename Run2 into Inv2. clear Run1.
      destruct Inv2 as [GetQ [Env Done]].
      cbn [state.inputs state.height state.queue state.env] in *.
      destruct (Done e ltac:(omega)) as [[]|[]].
      intuition.
    - simpl in *.
      left.
      exists (n1 + n2), e2, x.
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

  Theorem completeness :
    (exists e, forall x, P x e) ->
    exists n e,
      run n (state.init []) = inr e /\
      (forall x, P x e).
  Proof.
    assert (
    forall e,
      (forall x, P x e) ->
      forall n l,
      List.length (List.filter (check_inputs l) (expr.all_up_to_height (expr.height e))) <= n ->
      exists n1 e1,
        run n1 (state.init l) = inr e1
      ) as completeness'.
    {
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
    }
    intros [ewit Hwit].
    destruct (completeness' ewit Hwit _ [] (le_n _)) as [n [e Run]].
    exists n, e.
    split; eauto using run_inr, init_inv.
  Qed.
End cozy.

Print Assumptions completeness.