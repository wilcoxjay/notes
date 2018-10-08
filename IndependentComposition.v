Require Import Relations.Relation_Operators.

Module system.
  Record t := Make {
    state : Type;
    init : state -> Prop;
    step : state -> state -> Prop
  }.

  Definition reachable (S : t) (s : S.(state)) : Prop :=
    exists s0,
      S.(init) s0 /\
      clos_refl_trans_n1 _ S.(step) s0 s.

  Definition safety (S : t) (P : S.(state) -> Prop) : Prop :=
    forall s,
      reachable S s ->
      P s.
End system.

Section composition.
  Variables A B : system.t.

  Definition composition : system.t :=
    system.Make
      (A.(system.state) * B.(system.state))
      (fun '(a,b) => A.(system.init) a /\ B.(system.init) b)
      (fun '(a1,b1) '(a2, b2) =>
         (A.(system.step) a1 a2 /\ b1 = b2) \/
         (B.(system.step) b1 b2 /\ a1 = a2))
    .

  Variable safeA : A.(system.state) -> Prop.
  Hypothesis correctA : system.safety A safeA.

  Variable safeB : B.(system.state) -> Prop.
  Hypothesis correctB : system.safety B safeB.

  Definition safeC := fun '(a,b) => safeA a /\ safeB b.

  Lemma composition_reachable :
    forall a0 b0 a b,
      clos_refl_trans_n1 _ (system.step composition) (a0, b0) (a, b) ->
      clos_refl_trans_n1 _ (system.step A) a0 a /\
      clos_refl_trans_n1 _ (system.step B) b0 b.
  Proof.
    intros a0 b0 a b Reach.
    remember (a0,b0) as s0 eqn:E0.
    remember (a,b) as s eqn:E.
    revert a0 b0 E0 a b E.
    induction Reach; intros a0 b0 E0 a b E; subst.
    - inversion E; subst.
      split; constructor.
    - destruct y as [a1 b1].
      specialize (IHReach a0 b0 eq_refl a1 b1 eq_refl)
        as [ReachA ReachB].
      inversion H.
      + destruct H0 as [stepA ?]; subst.
        split; auto.
        econstructor; eauto.
      + destruct H0 as [stepB ?]; subst.
        split; auto.
        econstructor; eauto.
  Qed.

  Theorem correctC : system.safety composition safeC.
  Proof.
    unfold system.safety, safeC.
    intros [a b] [[a0 b0] [[InitA InitB] Reach]].
    apply composition_reachable in Reach as [ReachA ReachB].
    split.
    - apply correctA.
      exists a0; auto.
    - apply correctB.
      exists b0; auto.
  Qed.    
End composition.

Check composition.
Check correctC.