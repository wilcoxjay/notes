Require Import Setoid.

Set Implicit Arguments.
Ltac invc H := inversion H; subst; clear H.

Module paxos_epr.
Section paxos.
  Variables node value quorum round : Type.

  Variable none : round.

  Variable le : round -> round -> Prop.

  Hypothesis le_refl : forall X, le X X.
  Hypothesis le_trans : forall X Y Z, le X Y -> le Y Z -> le X Z.
  Hypothesis le_antisym : forall X Y, le X Y -> le Y X -> X = Y.
  Hypothesis le_total : forall X Y, le X Y \/ le Y X.

  Hypothesis round_eq_dec : forall R1 R2 : round, R1 = R2 \/ R1 <> R2.

  Variable member : node -> quorum -> Prop.

  Hypothesis quorum_intersection : forall Q1 Q2, exists N, member N Q1 /\ member N Q2.

  Record state :=
    {
      one_a : round -> Prop;
      one_b : node -> round -> Prop; 
      left_round : node -> round -> Prop;
      proposal : round -> value -> Prop;
      vote : node -> round -> value -> Prop;
      decision : round -> value -> Prop
    }.

  Definition init (s : state) : Prop :=
    (forall R, ~ one_a s R) /\
    (forall N R, ~ one_b s N R) /\
    (forall N R, ~ left_round s N R) /\
    (forall R V, ~ proposal s R V) /\
    (forall N R V, ~ vote s N R V) /\
    (forall R V, ~ decision s R V).
  
  Definition send_1a (s s' : state) : Prop :=
    exists r,
      r <> none /\
      (forall R, one_a s' R <-> one_a s R \/ R = r) /\

      (forall N R, one_b s' N R <-> one_b s N R) /\
      (forall N R, left_round s' N R <-> left_round s N R) /\
      (forall R V, proposal s' R V <-> proposal s R V) /\
      (forall N R V, vote s' N R V <-> vote s N R V) /\
      (forall R V, decision s' R V <-> decision s R V).


  Definition join_round (s s' : state) : Prop :=
    exists n r,
      r <> none /\
      one_a s r /\
      ~ left_round s n r /\
      (forall N R, one_b s' N R <-> one_b s N R \/ (N = n /\ R = r)) /\
      (forall N R, left_round s' N R <-> left_round s N R \/ (N = n /\ ~ le r R)) /\

      (forall R, one_a s' R <-> one_a s R) /\
      (forall R V, proposal s' R V <-> proposal s R V) /\
      (forall N R V, vote s' N R V <-> vote s N R V) /\
      (forall R V, decision s' R V <-> decision s R V).

  Definition propose (s s' : state) : Prop :=
    exists r q maxr v,
      r <> none /\
      (forall V, ~ proposal s r V) /\
      (forall N, member N q -> one_b s N r) /\
      ((maxr = none /\ (forall N MAXR V, ~ (member N q /\ ~ le r MAXR /\ vote s N MAXR V))) \/
       (maxr <> none /\
        (exists N, member N q /\ ~ le r maxr /\ vote s N maxr v) /\
        (forall N MAXR V, member N q -> ~ le r MAXR -> vote s N MAXR V -> le MAXR maxr))) /\
      (forall R V, proposal s' R V <-> proposal s R V \/ (R = r /\ V = v)) /\

      (forall R, one_a s' R <-> one_a s R) /\
      (forall N R, one_b s' N R <-> one_b s N R) /\
      (forall N R, left_round s' N R <-> left_round s N R) /\
      (forall N R V, vote s' N R V <-> vote s N R V) /\
      (forall R V, decision s' R V <-> decision s R V).

  Definition cast_vote (s s' : state) : Prop :=
    exists n v r,
      r <> none /\
      ~ left_round s n r /\
      proposal s r v /\
      (forall N R V, vote s' N R V <-> vote s N R V \/ (N = n /\ R = r /\ V = v)) /\

      (forall R, one_a s' R <-> one_a s R) /\
      (forall N R, one_b s' N R <-> one_b s N R) /\
      (forall N R, left_round s' N R <-> left_round s N R) /\
      (forall R V, proposal s' R V <-> proposal s R V) /\
      (forall R V, decision s' R V <-> decision s R V).

  Definition decide (s s' : state) : Prop :=
    exists r v q,
      r <> none /\
      (forall N, member N q -> vote s N r v) /\
      (forall R V, decision s' R V <-> decision s R V \/ (R = r /\ V = v)) /\

      (forall R, one_a s' R <-> one_a s R) /\
      (forall N R, one_b s' N R <-> one_b s N R) /\
      (forall N R, left_round s' N R <-> left_round s N R) /\
      (forall R V, proposal s' R V <-> proposal s R V) /\
      (forall N R V, vote s' N R V <-> vote s N R V).

  Inductive next : state -> state -> Prop :=
  | next_send_1a : forall s s', send_1a s s' -> next s s'
  | next_join_round : forall s s', join_round s s' -> next s s'
  | next_propose : forall s s', propose s s' -> next s s'
  | next_cast_vote : forall s s', cast_vote s s' -> next s s'
  | next_decide : forall s s', decide s s' -> next s s'
  .

  Definition safety (s : state) : Prop :=
    forall R1 V1 R2 V2,
      decision s R1 V1 ->
      decision s R2 V2 ->
      V1 = V2.

  Definition choosable (s : state) r v : Prop :=
    exists q,
      forall n,
        member n q ->
        ~ left_round s n r \/ vote s n r v.

  Definition inv (s : state) : Prop :=
    (forall R V1 V2,
        proposal s R V1 ->
        proposal s R V2 ->
        V1 = V2) /\
    (forall N R V,
        vote s N R V ->
        proposal s R V) /\
    (forall N V,
        ~ vote s N none V) /\
    (forall N R1 R2,
        one_b s N R2 ->
        ~ le R2 R1 ->
        left_round s N R1) /\
    (forall R1 V1 R2 V2,
        choosable s R1 V1 ->
        ~ le R2 R1 ->
        proposal s R2 V2 ->
        V1 = V2) /\
    (forall R V,
        decision s R V ->
        exists q,
          forall n,
            member n q ->
            vote s n R V)
  .

  Lemma lt_eq_gt_dec :
    forall R1 R2,
      ~ le R2 R1 \/ R1 = R2 \/ ~ le R1 R2.
  Proof.
    intros R1 R2.
    destruct (le_total R1 R2), (round_eq_dec R1 R2); auto 10.
  Qed.

  Lemma init_inv :
    forall s,
      init s ->
      inv s.
  Proof.
    firstorder.
  Qed.

  Lemma inv_safety :
    forall s,
      inv s ->
      safety s.
  Proof.
    unfold inv, safety.

    intros s (PropUniq & VoteProp & _ & _ & Choose & Dec) R1 V1 R2 V2.
    intros [Q1 HQ1]%Dec [Q2 HQ2]%Dec.
    destruct (quorum_intersection Q1 Q2) as (n & Hn1 & Hn2).
    pose proof HQ1 _ Hn1 as Vote1.
    pose proof HQ2 _ Hn2 as Vote2.
    assert (choosable s R1 V1) by (unfold choosable; eauto).
    assert (choosable s R2 V2) by (unfold choosable; eauto).
    destruct (lt_eq_gt_dec R1 R2) as [|[|]]; subst; eauto using eq_sym.
  Qed.
    
  Lemma choosable_frame :
    forall s s',
      (forall N R, left_round s' N R <-> left_round s N R) ->
      (forall N R V, vote s' N R V <-> vote s N R V) ->
      forall R V, choosable s' R V <-> choosable s R V.
  Proof.
    intros s s' FLR FV R V.
    unfold choosable.
    split; intros [q H]; exists q; intros n; specialize (H n);
      rewrite FLR, FV in *; auto.
  Qed.

  Lemma next_inv :
    forall s s',
      inv s ->
      next s s' ->
      inv s'.
  Proof.
    unfold inv.
    intros s s' (PU & VP & Vnone & LR & Choose & Dec) Next.
    invc Next; [
      destruct H as (r & NN & I1a & F1b & FLR & FP & FV & FD)
    | destruct H as (n & r & NN & H1a & HNLR & I1b & ILR & F1a & FP & FV & FD)
    | destruct H as (r & q & maxr & v & NN & HNP & H1b & HMR & IP & F1a & F1b & FLR & FV & FD)
    | destruct H as (n & v & r & NN & HLR & HP & IV & F1a & F1b & FLR & FP & FD)
    | destruct H as (r & v & q & NN & HV & ID & F1a & F1b & FLR & FP & FV)
    ]; repeat split; intros *;
      rewrite ?F1b, ?FLR, ?FP, ?FV, ?FD; try rewrite choosable_frame by eassumption; eauto;
    try solve [
          let q := fresh q in
          let n := fresh n in
          intros D;
          pose proof Dec R V D as [q H];
          exists q; intros n; specialize (H n);
          now rewrite FV
        ].
    - rewrite I1b, ILR.
      specialize (LR N R1 R2).
      intuition. subst. auto.
    - intros [q C] LE P.
      apply Choose with (R1 := R1) (R2 := R2); auto.
      exists q.
      intros n1.
      specialize (C n1).
      rewrite ILR, FV in C.
      intuition.
    - rewrite !IP.
      intros [|[]] [|[]]; subst; firstorder.
    - intros *. rewrite IP. eauto.
    - intros *. 
      rewrite IP. intros C LE [P|[-> ->]]. eauto.
      pose proof C as C'.
      destruct C as [Q HQ].
      destruct (quorum_intersection q Q) as (w & W1 & W2).
      destruct (HQ _ W2).
      + specialize (H1b _ W1).
        specialize (LR _ _ _ H1b LE).
        contradiction.
      + destruct HMR as [[->HMR]|(EMR & (N & M & LER & V) & HMR)].
        specialize (HMR w R1 V1). now intuition.
        specialize (HMR w R1 V1 ltac:(assumption) ltac:(assumption) ltac:(assumption)).
        apply VP in V.
        destruct (round_eq_dec R1 maxr).
        * subst. eauto.
        * eapply Choose; try apply V; eauto.
    - rewrite IV. intuition; subst; eauto.
    - rewrite IV. intros [|(-> & <- & ->)]. eapply Vnone; eauto. congruence.
    - assert (forall R V, choosable s' R V -> choosable s R V) as FC.
      {
        unfold choosable.
        intros R V (q & H).
        exists q.
        intros n1 M.
        specialize (H n1 M).
        rewrite FLR, IV in H.
        intuition; subst; auto.
      }
      intros C%FC. eauto.
    - intros D.
      pose proof Dec R V D as [q H].
      exists q. intros n1 M. specialize (H n1 M).
      rewrite IV. auto.
    - intros *. rewrite ID.
      intros [D|[-> ->]].
      + destruct (Dec R V D) as (q1 & H). exists q1.
        intros n1 M1.
        rewrite FV.
        auto.
      + exists q. intros. rewrite FV. auto.
  Qed.      
End paxos.
End paxos_epr.