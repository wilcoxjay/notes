Require Import List Omega.
Import ListNotations.

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

Lemma all_up_to_height_sanify :
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
    apply all_up_to_height_sanify in Il.
    apply IHn in Ir.
    zify. omega.
Qed.

Definition eq_mod (l : list nat) (e1 e2 : t) : Prop :=
  Forall (fun x => expr.eval x e1 = expr.eval x e2) l.

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

End expr.

Definition extensional (P : expr.t -> Prop) : Prop :=
  forall e1 e2,
    expr.sem_eq e1 e2 ->
    P e1 <-> P e2.

Module state.
  Record t := Make { height: nat; queue : list expr.t; inputs: list nat }.

  Definition init : t :=
    Make 0 [] [].
End state.

Section cozy.

  Variable P : nat -> expr.t -> Prop.
  Hypothesis P_ext : forall x, extensional (P x).

  Hypothesis P_dec : forall x e, {P x e} + {~ P x e}.

  Hypothesis P_oracle : forall e, {x : nat | ~ P x e} + {forall x, P x e}.

  Definition check_inputs (e : expr.t) : forall l, {Forall (fun x => P x e) l} + {Exists (fun x => ~ P x e) l} :=
    fix go (l : list nat) :=
      match l with
      | [] => left (Forall_nil _)
      | x :: l =>
        match P_dec x e with
        | left pf =>
          match go l with
          | left IHpf => left (Forall_cons _ pf IHpf)
          | right pf => right (Exists_cons_tl _ pf)
          end
        | right pf => right (Exists_cons_hd _ x l pf)
        end
      end.

  Definition step (s : state.t) : state.t + expr.t :=
    match s.(state.queue) with
    | [] => inl (state.Make (S s.(state.height))
                           (expr.all_of_exactly_height (S s.(state.height)))
                           s.(state.inputs))
    | e :: q =>
      match check_inputs e s.(state.inputs) with
      | left pf =>
        match P_oracle e with
        | inleft (exist _ x pf) => inl (state.Make s.(state.height) q (x :: s.(state.inputs)))
        | inright _ => inr e
        end
      | right pf => inl (state.Make s.(state.height) q s.(state.inputs))
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
    forall e,
      expr.height e <= s.(state.height) ->
      (exists x, ~P x e) \/ (exists e', In e' s.(state.queue) /\ expr.sem_eq e e').

  Lemma init_inv :
    inv state.init.
  Proof.
    unfold inv, state.init.
    simpl.
    intros e Height.
    destruct e; simpl in *; omega.
  Qed.

  Lemma step_inr :
    forall s e,
      inv s ->
      step s = inr e ->
      forall x, P x e.
  Proof.
    unfold step.
    intros s e Inv Step.
    destruct state.queue; [discriminate|].
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
      cbn -[In expr.all_of_exactly_height].
      intros e LE.
      inversion LE.
      + auto using expr.all_of_exactly_height_complete.
      + unfold inv in Inv.
        rewrite EQ in *.
        specialize (Inv e H0).
        destruct Inv as [[x HP]|[e' [I SE]]].
        * eauto.
        * intuition.
    - destruct check_inputs.
      + destruct P_oracle as [[x pf]|]; [|discriminate].
        inversion Step; subst; clear Step.
        unfold inv in *.
        simpl.
        intros e Height.
        destruct (Inv e Height) as [[x0 pf0]| I].
        * now eauto.
        * rewrite EQ in I.
          simpl in I. destruct I as [e' [[?|I] SE]].
          -- subst. left. exists x.
             intro C.
             unfold extensional in P_ext.
             rewrite P_ext in C by eauto.
             auto.
          -- eauto.
      + inversion Step; subst; clear Step.
        unfold inv in *.
        simpl.
        intros e2 Height2.
        destruct (Inv e2 Height2) as [[x pf]| I].
        * now eauto.
        * rewrite EQ in I.
          simpl in I. destruct I as [e' [[?|I] SE]].
          -- subst.
             rewrite Exists_exists in e.
             destruct e as [x0 [_ pf0]].
             left. exists x0.
             intro C.
             unfold extensional in P_ext.
             rewrite P_ext in C by eauto.
             auto.
          -- eauto.
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

  Lemma run_skipn :
    forall n s,
      n <= List.length s.(state.queue) ->
      (exists l, run n s = inl (state.Make s.(state.height)
                                      (skipn n s.(state.queue))
                                      (l ++ s.(state.inputs)))) \/
      (exists e, run n s = inr e).
  Proof.
    induction n; intros s LE.
    - left. exists []. destruct s; reflexivity.
    - set (r := run (S n) s).
      cbn [run] in *.
      unfold step in *.
      destruct state.queue eqn:EQ; [simpl in *; omega|].
      destruct check_inputs.
      + destruct P_oracle as [[x Hx]|].
        * match goal with
          | [ _ := run n ?s |- _ ] =>
            specialize (IHn s ltac:(simpl in *; omega))
          end.
          subst r.
          simpl in *.
          destruct IHn as [[l0 Run]|[e0 Run]]; rewrite Run.
          -- left.
             exists (l0 ++ [x]).
             now rewrite app_ass.
          -- right.
             eauto.
        * right. subst r. eauto.
      + match goal with
        | [ _ := run n ?s |- _ ] =>
          specialize (IHn s ltac:(simpl in *; omega))
        end.
        subst r.
        simpl in *.
        destruct IHn as [[l0 Run]|[e0 Run]]; rewrite Run; eauto.
  Qed.

  Lemma skipn_length :
    forall A n (l : list A),
      List.length l <= n ->
      skipn n l = [].
  Proof.
    induction n; destruct l; simpl; intros LE; try omega; auto with *.
  Qed.

  Lemma finish_this_height :
    forall s,
      exists n,
        (exists l, run n s = inl (state.Make s.(state.height) [] (l ++ s.(state.inputs)))) \/
        (exists e, run n s = inr e).
  Proof.
    intros s.
    destruct (run_skipn (List.length s.(state.queue)) s ltac:(omega)) as [[l Run]|[e Run]].
    - rewrite skipn_length in Run by omega.
      eauto.
    - eauto.
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

  Lemma all_heights :
    forall h,
      exists n,
        (exists l, run n state.init = inl (state.Make h (expr.all_of_exactly_height h) l)) \/
        (exists e, run n state.init = inr e).
  Proof.
    induction h.
    - exists 0. left. exists []. reflexivity.
    - destruct IHh as [n1 [[l1 Run1]|[e Run]]].
      + match goal with
        | [ _ : _ = inl ?s |- _ ] =>
          destruct (finish_this_height s) as [n2 [[l2 Run2]|[e Run]]]
        end.
        * exists (n1 + (n2 + 1)).
          left.
          eexists.
          now rewrite run_plus, Run1, run_plus, Run2.
        * exists (n1 + n2).
          right.
          rewrite run_plus, Run1, Run. eauto.
      + exists n1. right. eauto.
  Qed.

  Theorem completeness :
    (exists e, forall x, P x e) ->
    exists n e,
      run n state.init = inr e /\
      (forall x, P x e).
  Proof.
    intros [ewit Hewit].

    destruct (all_heights (expr.height ewit)) as [n [[l Run]|[e Run]]].
    - match goal with
      | [ H : run _ _ = inl ?ms |- _ ] =>
        set (s := ms) in *;
        destruct (finish_this_height s) as [n2 [[l2 Run2]|[e Run2]]]
      end.
      + match goal with
        | [ H : run _ _ = inl ?ms |- _ ] =>
          set (s2 := ms) in *
        end.
        assert (inv s2) as Inv2 by eauto using run_inl, init_inv.
        unfold inv in Inv2.
        subst s2 s. simpl in *.
        specialize (Inv2 ewit ltac:(omega)).
        firstorder.
      + exists (n + n2), e.
        rewrite run_plus, Run, Run2.
        split; eauto using run_inr, run_inl, init_inv.
    - exists n, e.
        split; eauto using run_inr, init_inv.
  Qed.
End cozy.
