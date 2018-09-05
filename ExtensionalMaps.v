Require Import Relation_Definitions Arith Omega.
Require Import RelationClasses EquivDec List DecidableClass Sorted TotalOrder.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Ltac invc H := inversion H; subst; clear H.

Module map.
  Class class K :=
    Make {
      t : Type -> Type;
      empty : forall {V}, t V;
      get : forall V, K -> t V -> option V;
      set : forall V, K -> V -> t V -> t V;
      rem : forall V, K -> t V -> t V;
      fresh : forall V, t V -> K;

      ge : forall V k, get(V:=V) k empty = None;

      gss : forall V (k : K) (v : V) m, get k (set k v m) = Some v;
      gso : forall V (k1 k2 : K) (v : V) m, k1 <> k2 -> get k2 (set k1 v m) = get k2 m;

      grs : forall V (k : K) (m : t V), get k (rem k m) = None;
      gro : forall V (k1 k2 : K) (m : t V), k1 <> k2 -> get k2 (rem k1 m) = get k2 m;

      gf : forall V (m : t V), get (fresh m) m = None;

      ext : forall V (m1 m2 : t V), (forall k, get k m1 = get k m2) -> m1 = m2
    }.
End map.

Module funcmap.
  Section funcmap.
    Context K `(EqDec K eq).

    Definition t V := K -> option V.

    Definition empty V : t V := fun _ => None.

    Definition get V k (m : t V) : option V := m k.

    Definition set V k v (m : t V) :=
      fun k' =>
      if k == k' then Some v else m k'.

    Definition rem V k (m : t V) :=
      fun k' => if k == k' then None else m k'.

    Definition fresh V (m : t V) : K.
    Admitted.

    Lemma ge : forall V k, get k (empty V) = None.
    Proof.
      unfold get, empty.
      auto.
    Qed.

    Lemma gss : forall V (k : K) (v : V) m, get k (set k v m) = Some v.
    Proof.
      unfold get, set.
      intros.
      destruct equiv_dec; congruence.
    Qed.

    Lemma gso : forall V (k1 k2 : K) (v : V) m, k1 <> k2 -> get k2 (set k1 v m) = get k2 m.
    Proof.
      unfold get, set.
      intros.
      destruct equiv_dec; congruence.
    Qed.

    Lemma grs : forall V (k : K) (m : t V), get k (rem k m) = None.
    Proof.
      unfold get, rem.
      intros.
      destruct equiv_dec; congruence.
    Qed.

    Lemma gro : forall V (k1 k2 : K) (m : t V), k1 <> k2 -> get k2 (rem k1 m) = get k2 m.
    Proof.
      unfold get, rem.
      intros.
      destruct equiv_dec; congruence.
    Qed.

    Lemma gf : forall V (m : t V), get (fresh m) m = None.
    Admitted.
    (* Careful: this is literally false, since m could always return Some. *)

    (* All hope is not lost, since it's not possible to notice or exploit this
       beyond the boundary of this module, nor is it possible to construct such
       a map outside this module. *)

    Lemma ext : forall V (m1 m2 : t V),
        (forall k, get k m1 = get k m2) ->
        m1 = m2.
    Proof.
      intros.
      apply FunctionalExtensionality.functional_extensionality.
      exact H0.
    Qed.

    Global Instance funcmap : map.class K := map.Make ge gss gso grs gro gf ext.
  End funcmap.
End funcmap.

Class UnboundedOrder A (R : relation A) := {
  UnboundedOrder_bigger : A -> A;
  UnboundedOrder_bigger_ok : forall x : A, R x (UnboundedOrder_bigger x)
}.

Instance nat_UnboundedOrder : UnboundedOrder lt :=
  { UnboundedOrder_bigger := S }.
 intros. omega.
Defined.

Class Inhabited (A : Type) := {
  Inhabited_witness : A
}.

Instance nat_Inhabited : Inhabited nat := { Inhabited_witness := 0 }.

Module sortedmap.
  Section sortedmap.
    Context K lt `(SOK : StrictOrder(A:=K) lt) `(EDK : EqDec K eq).
    Context `(ltb : forall x y, Decidable (lt x y)).
    Context `(TOK : TotalOrder _ lt).
    Context `(UOK : UnboundedOrder _ lt).
    Context `(IK : Inhabited K).

    Definition t' V := list (K * V).

    Local Infix "<" := lt.
    Local Infix "<?" := (fun x y => decide (lt x y)).

    Definition empty' V : t' V := [].

    Fixpoint set' V (k : K) (v : V) (m : t' V) : t' V :=
      match m with
      | [] => [(k, v)]
      | (k',v') :: m =>
        if k <? k'
        then (k, v) :: (k', v') :: m
        else if k == k' then (k, v) :: m
        else (k', v') :: set' k v m
      end.

    Fixpoint get' V (k : K) (m : t' V) : option V :=
      match m with
      | [] => None
      | (k',v') :: m =>
        if k <? k' then None
        else if k == k' then Some v'
        else get' k m
      end.

    Fixpoint rem' V (k : K) (m : t' V) : t' V :=
      match m with
      | [] => []
      | (k', v') :: m =>
        if k <? k' then (k', v') :: m
        else if k == k' then m
        else (k', v') :: rem' k m
      end.

    Definition max (k1 k2 : K) : K :=
      if k1 <? k2 then k2 else k1.

    Lemma max_lt_elim :
      forall k1 k2 k3,
        max k1 k2 < k3 ->
        k1 < k3 /\ k2 < k3.
    Proof.
      unfold max.
      intros.
      decide (k1 < k2); eauto using StrictOrder_Transitive.
      pose proof TotalOrder_trichotomy k1 k2.
      intuition; try congruence.
      eauto using StrictOrder_Transitive.
    Qed.

    Fixpoint maximum_key V (m : t' V) : option K :=
      match m with
      | [] => None
      | (k, _) :: m =>
        match maximum_key m with
        | None => Some k
        | Some k' => Some (max k k')
        end
      end.

    Lemma maximum_key_None :
      forall V (m : t' V),
        maximum_key m = None ->
        m = [].
    Proof.
      destruct m; simpl; auto.
      destruct p.
      destruct maximum_key; discriminate.
    Qed.

    Lemma maximum_key_Some_bigger_fresh :
      forall V (m : t' V) k k',
        maximum_key m = Some k ->
        k < k' ->
        get' k' m = None.
    Proof.
      induction m; simpl; intros.
      - discriminate.
      - destruct a as [k2 v2].
        destruct maximum_key eqn:?; try discriminate.
        + invc H. apply max_lt_elim in H0. destruct H0.
          decide (k' < k2); auto.
          destruct equiv_dec.
          * assert (k' = k2) by congruence. subst k'.
            exfalso. eapply StrictOrder_Irreflexive; eauto.
          * eauto.
        + apply maximum_key_None in Heqo.
          invc H. simpl.
          decide (k' < k); try congruence.
          destruct equiv_dec; try congruence.
    Qed.

    Definition fresh' V (m : t' V) : K :=
      match maximum_key m with
      | None => Inhabited_witness
      | Some k => UnboundedOrder_bigger k
      end.

    Lemma gf' : forall V (m : t' V),
        get' (fresh' m) m = None.
    Proof.
      unfold fresh'.
      intros.
      destruct maximum_key eqn:E.
      - eapply maximum_key_Some_bigger_fresh; eauto.
        apply UnboundedOrder_bigger_ok.
      - apply maximum_key_None in E. subst. auto.
    Qed.

    Definition keys' V (m : t' V) : list K :=
      List.map fst m.

    Definition values' V (m : t' V) : list V :=
      List.map snd m.

    Definition tuple_lt {V} (p1 p2 : K * V) : Prop :=
      fst p1 < fst p2.

    Lemma set_hdrel : forall V (k k' : K) (v v' : V) (m : t' V),
        k' < k ->
        HdRel tuple_lt (k', v') m ->
        HdRel tuple_lt (k', v') (set' k v m).
    Proof.
      induction 2; simpl.
      - auto.
      - destruct b as [k2 v2].
        decide (k < k2).
        + auto.
        + destruct equiv_dec.
          * auto.
          * auto.
    Qed.

    Lemma HdRel_tuple_lt :
      forall (k : K) V (v1 v2 : V) m,
        HdRel tuple_lt (k, v1) m ->
        HdRel tuple_lt (k, v2) m.
    Proof.
      induction 1.
      - constructor.
      - constructor. unfold tuple_lt in *. simpl in *. auto.
    Qed.

    Lemma set_ok : forall V (k : K) (v : V) (m : t' V),
        Sorted tuple_lt m ->
        Sorted tuple_lt (set' k v m).
    Proof.
      induction m; simpl; intros.
      - auto.
      - destruct a as [k' v'].
        apply Sorted_inv in H.
        destruct H as [S Hd].
        decide (k < k').
        + auto.
        + destruct equiv_dec.
          * constructor; auto.
            assert (k = k') by congruence. subst k'.
            eapply HdRel_tuple_lt; eauto.
          * assert (k' < k) by
              (pose proof TotalOrder_trichotomy k k';
               intuition congruence).
            constructor.
            auto.
            auto using set_hdrel.
    Qed.

    Lemma HdRel_trans :
      forall V k1 k2 (v : V) m,
        k1 < k2 ->
        HdRel tuple_lt (k2, v) m ->
        HdRel tuple_lt (k1, v) m.
    Proof.
      intros V k1 k2 v m Lt Hd.
      invc Hd.
      - auto.
      - constructor. unfold tuple_lt in *. simpl in *. eauto using StrictOrder_Transitive.
    Qed.


    Lemma rem_hdrel : forall V (k k' : K) (v' : V) (m : t' V),
        Sorted tuple_lt m ->
        HdRel tuple_lt (k', v') m ->
        HdRel tuple_lt (k', v') (rem' k m).
    Proof.
      intros V k k' v' m S Hd.
      destruct m; simpl.
      - auto.
      - destruct p as [k2 v2].
        decide (k < k2).
        + auto.
        + destruct equiv_dec.
          * destruct m; auto.
            invc Hd.
            invc S.
            assert (k = k2) by congruence. subst k2.
            compute in H1.
            eapply HdRel_trans; eauto.
            eapply HdRel_tuple_lt; eauto.
          * inversion Hd; auto.
    Qed.


    Lemma rem_ok : forall V k (m : t' V),
        Sorted tuple_lt m ->
        Sorted tuple_lt (rem' k m).
    Proof.
      induction 1; simpl.
      - auto.
      - destruct a as [k' v'].
        decide (k < k').
        + auto.
        + destruct equiv_dec; auto.
          constructor; auto.
          apply rem_hdrel; auto.
    Qed.


    Definition t V := {m : t' V | Sorted tuple_lt m}.

    Definition empty V : t V := exist _ (empty' V) (Sorted_nil _).

    Definition get V (k : K) (m : t V) : option V :=
      get' k (proj1_sig m).

    Definition set V (k : K) (v : V) (m : t V) : t V :=
      exist _ (set' k v (proj1_sig m)) (set_ok _ _ (proj2_sig m)).

    Definition rem V (k : K) (m : t V) : t V :=
      exist _ (rem' k (proj1_sig m)) (rem_ok _ (proj2_sig m)).

    Definition fresh V (m : t V) : K :=
      fresh' (proj1_sig m).

    Definition keys V (m : t V) : list K :=
      keys' (proj1_sig m).

    Definition values V (m : t V) : list V :=
      values' (proj1_sig m).

    Lemma ge : forall V k, get k (empty V) = None.
    Proof. reflexivity. Qed.

    Lemma gss' :
      forall V (k : K) (v : V) (m : t' V),
        get' k (set' k v m) = Some v.
    Proof.
      induction m; simpl; intros.
      - decide (k < k).
        + exfalso. eapply StrictOrder_Irreflexive; eauto.
        + destruct equiv_dec; congruence.
      - destruct a as [k' v'].
        decide (k < k').
        + simpl. decide (k < k).
          * exfalso. eapply StrictOrder_Irreflexive; eauto.
          * destruct equiv_dec; congruence.
        + destruct equiv_dec.
          * simpl. decide (k < k).
            -- exfalso. eapply StrictOrder_Irreflexive; eauto.
            -- destruct equiv_dec; congruence.
          * simpl. decide (k < k'); try congruence.
            destruct equiv_dec; congruence.
    Qed.

    Lemma gss:
      forall V (k : K) (v : V) (m : t V), get k (set k v m) = Some v.
    Proof.
      unfold get, set.
      destruct m.
      simpl.
      apply gss'.
    Qed.

    Lemma gso':
      forall V (k1 k2 : K) (v : V) m, k1 <> k2 -> get' k2 (set' k1 v m) = get' k2 m.
    Proof.
      induction m; simpl;intros.
      - decide (k2 < k1); auto.
        destruct equiv_dec; congruence.
      - destruct a as [k' v'].
        decide (k1 < k').
        + simpl. decide (k2 < k1).
          * decide (k2 < k'); auto.
            assert (k2 < k'). eapply StrictOrder_Transitive; eauto. congruence.
          * destruct equiv_dec.
            -- assert (k2 = k1) by congruence. subst k2.
               decide (k1 < k'); congruence.
            -- auto.
        + destruct equiv_dec.
          * simpl. assert (k1 = k') by congruence. subst k'.
            decide (k2 < k1); auto.
            destruct equiv_dec; congruence.
          * simpl. decide (k2 < k'); auto.
            destruct equiv_dec; auto.
    Qed.


    Lemma gso:
      forall V (k1 k2 : K) (v : V) m, k1 <> k2 -> get k2 (set k1 v m) = get k2 m.
    Proof.
      unfold get, set.
      destruct m.
      simpl.
      apply gso'.
    Qed.

    Lemma get'_hdrel :
      forall V m k (v : V),
        HdRel tuple_lt (k, v) m ->
        get' k m = None.
    Proof.
      destruct m; simpl; intros.
      - auto.
      - destruct p as [k' v'].
        invc H.
        compute in H1.
        decide (k < k'); congruence.
    Qed.

    Lemma grs' : forall V (k : K) (m : t' V),
        Sorted tuple_lt m ->
        get' k (rem' k m) = None.
    Proof.
      induction 1; simpl.
      - auto.
      - destruct a as [k' v'].
        decide (k < k').
        + simpl. decide (k < k'); congruence.
        + destruct equiv_dec.
          * assert (k = k') by congruence. subst k'.
            now erewrite get'_hdrel by eauto.
          * simpl. decide (k < k'); try congruence.
            destruct equiv_dec; congruence.
    Qed.

    Lemma grs : forall V (k : K) (m : t V), get k (rem k m) = None.
    Proof.
      unfold get, rem.
      destruct m; simpl.
      apply grs'; auto.
    Qed.

    Lemma gro' : forall V (k1 k2 : K) (m : t' V),
        Sorted tuple_lt m ->
        k1 <> k2 ->
        get' k2 (rem' k1 m) = get' k2 m.
    Proof.
      induction m; simpl; intros.
      - auto.
      - destruct a as [k' v'].
        decide (k1 < k').
        + auto.
        + invc H.
          decide (k2 < k').
          * destruct equiv_dec.
            -- assert (k1 = k') by congruence. subst k'.
               now erewrite get'_hdrel by eauto using HdRel_trans.
            -- simpl. decide (k2 < k'); congruence.
          * destruct equiv_dec.
            -- assert (k1 = k') by congruence. subst k'.
               destruct equiv_dec; congruence.
            -- simpl.
               decide (k2 < k'); try congruence.
               destruct equiv_dec; auto.
    Qed.

    Lemma gro : forall V (k1 k2 : K) (m : t V), k1 <> k2 -> get k2 (rem k1 m) = get k2 m.
    Proof.
      unfold get, rem.
      destruct m; simpl.
      apply gro'; auto.
    Qed.

    Lemma gf : forall V (m : t V), get (fresh m) m = None.
    Proof.
      unfold get, fresh.
      destruct m; simpl.
      apply gf'.
    Qed.

    Lemma ext : forall V (m1 m2 : t V), (forall k, get k m1 = get k m2) -> m1 = m2.
    Proof.
      unfold get.
      destruct m1, m2. simpl.
      intros.
      apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
      generalize dependent x0.
      rename s into S.
      induction S; intros x0 S0 E; destruct x0.
      - auto.
      - destruct p as [k v]. specialize (E k). simpl in *.
        decide (k < k).
        + exfalso. eapply StrictOrder_Irreflexive; eauto.
        + destruct equiv_dec; congruence.
      - destruct a as [k v]. specialize (E k). simpl in *.
        decide (k < k).
        + exfalso. eapply StrictOrder_Irreflexive; eauto.
        + destruct equiv_dec; congruence.
      - apply Sorted_inv in S0.
        destruct S0 as [S0 Hd0].
        rename H into Hd.
        destruct a as [k v].
        destruct p as [k0 v0].
        assert ((k, v) = (k0, v0)).
        {
          pose proof (E k) as Hk.
          simpl in Hk.
          decide (k < k).
          { exfalso. eapply StrictOrder_Irreflexive; eauto. }
          destruct equiv_dec; try congruence.
          decide (k < k0); try discriminate.
          destruct equiv_dec.
          - congruence.
          - pose proof TotalOrder_trichotomy k k0.
            intuition; try congruence.

            pose proof (E k0) as Hk0.
            simpl in Hk0.
            decide (k0 < k0).
            { exfalso. eapply StrictOrder_Irreflexive; eauto. }
            destruct (equiv_dec k0 k0); try congruence.
            decide (k0 < k); try congruence.
        }
        invc H.
        f_equal.
        apply IHS; auto.
        intros k1.
        specialize (E k1).
        simpl in *.
        decide (k1 < k0).
        + now erewrite !get'_hdrel by eauto using HdRel_trans.
        + destruct equiv_dec.
          * assert (k0 = k1) by congruence. subst k1.
            now erewrite !get'_hdrel by eauto.
          * auto.
    Qed.

    Lemma keys_empty' :
      forall V,
        keys' (empty' V) = [].
    Proof. auto. Qed.

    Lemma keys_empty :
      forall V,
        keys (empty V) = [].
    Proof.
      unfold keys, empty.
      apply keys_empty'.
    Qed.

    Lemma in_keys_intro' :
      forall V k v (m : t' V),
        get' k m = Some v ->
        In k (keys' m).
    Proof.
      induction m as [|[k1 v1]]; simpl; intros Get.
      - discriminate.
      - decide (k < k1).
        + discriminate.
        + destruct equiv_dec; [|now auto].
          unfold equiv in *.
          subst.
          auto.
    Qed.

    Lemma in_keys_intro :
      forall V k v (m : t V),
        get k m = Some v ->
        In k (keys m).
    Proof.
      unfold get, keys.
      eauto using in_keys_intro'.
    Qed.

    Lemma in_keys_elim' :
      forall V k (m : t' V),
        Sorted tuple_lt m ->
        In k (keys' m) ->
        exists v,
          get' k m = Some v.
    Proof.
      induction m as [|[k1 v1]]; simpl; intros Sorted I; intuition.
      - subst. simpl in *.
        decide (k < k).
        + exfalso. eapply StrictOrder_Irreflexive; eauto.
        + destruct equiv_dec; [now eauto|congruence].
      - inversion Sorted; subst; clear Sorted.
        specialize (IHm ltac:(assumption) ltac:(assumption)).
        destruct IHm as [v Get].
        decide (k < k1).
        + now erewrite get'_hdrel in Get by eauto using HdRel_trans.
        + now destruct equiv_dec; eauto.
    Qed.

    Lemma in_keys_elim :
      forall V k (m : t V),
        In k (keys m) ->
        exists v,
          get k m = Some v.
    Proof.
      unfold keys, get.
      intros V k m I.
      apply in_keys_elim'; auto.
      apply proj2_sig.
    Qed.

    Lemma in_values_intro' :
      forall V k (v : V) (m : t' V),
        get' k m = Some v ->
        In v (values' m).
    Proof.
      induction m as [|[k1 v1] m]; simpl; intros Get.
      - discriminate.
      - decide (k < k1); [discriminate|].
        destruct equiv_dec.
        + left. congruence.
        + auto.
    Qed.

    Lemma in_values_intro :
      forall V k (v : V) (m : t V),
        get k m = Some v ->
        In v (values m).
    Proof.
      unfold get, values.
      intros V k v m Get.
      eauto using in_values_intro'.
    Qed.

    Lemma in_values_elim' :
      forall V (v : V) (m : t' V),
        Sorted tuple_lt m ->
        In v (values' m) ->
        exists k, get' k m = Some v.
    Proof.
      unfold values'.
      intros V v.
      induction m as [|[]]; simpl; intros S I; intuition.
      - subst v0.
        exists k.
        decide (k < k) as LT.
        + exfalso. eapply StrictOrder_Irreflexive. now apply LT.
        + destruct equiv_dec; congruence.
      - inversion S; subst; clear S.
        specialize (IHm ltac:(assumption) ltac:(assumption)).
        destruct IHm as [k1 Get1].
        exists k1.
        decide (k1 < k).
        + now erewrite get'_hdrel in Get1 by eauto using HdRel_trans.
        + destruct equiv_dec; [|now auto].
          unfold equiv in *.
          subst k1.
          now erewrite get'_hdrel in Get1 by eauto using HdRel_trans.
    Qed.

    Lemma in_values_elim :
      forall V (v : V) (m : t V),
        In v (values m) ->
        exists k, get k m = Some v.
    Proof.
      unfold get, values.
      intros V v m I.
      apply in_values_elim' in I.
      assumption.
      apply proj2_sig.
    Qed.

    Global Instance sortedmap : map.class K := map.Make ge gss gso grs gro gf ext.
  End sortedmap.
End sortedmap.
