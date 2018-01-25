Fixpoint narg (n : nat) (T : Type) (U : Type) : Type :=
  match n with
  | 0 => U
  | S n' => T -> (narg n' T U)
  end.

Fixpoint narg_ext_eq (n : nat) {T U} (R : U -> U -> Prop) : narg n T U -> narg n T U -> Prop :=
  match n with
  | 0 => R
  | S n => fun A B => forall t, narg_ext_eq n R (A t) (B t)
  end.

Lemma narg_ext_eq_refl :
  forall T U (R : U -> U -> Prop) n (A : narg n T U),
    (forall u, R u u) ->
    narg_ext_eq n R A A.
Proof.
  induction n; simpl; auto.
Qed.


Lemma narg_ext_eq_trans :
  forall T U (R : U -> U -> Prop) n (A B C : narg n T U),
    (forall u1 u2 u3, R u1 u2 -> R u2 u3 -> R u1 u3) ->
    narg_ext_eq n R A B ->
    narg_ext_eq n R B C ->
    narg_ext_eq n R A C.
Proof.
  induction n; simpl; intros A B C Htrans; eauto.
Qed.

Definition ncompose {n : nat} {T U V : Type} (f : U -> V) (g : narg n T U) : narg n T V.
induction n; simpl in *; auto.
Defined.

Fixpoint nlist (n : nat) (T : Type) : narg n T (list T) :=
  match n with
  | 0 => nil
  | S n' => fun t => ncompose (fun x => cons t x) (nlist n' T)
  end.

Fixpoint nforall (n : nat) (T : Type) {struct n} : narg n T Prop -> Prop :=
  match n with
  | 0 => fun P => P
  | S n' => fun P => forall (t : T), nforall n' T (P t)
  end.

Definition has_length_n (n : nat) (T : Type) (l : list T) : Prop :=
  length l = n.

Lemma ncompose_compose :
  forall T U V W (f : U -> V) (g : V -> W) (R : W -> W -> Prop) n (x : narg n T U),
    (forall u, R (g (f u)) (g (f u))) ->
    narg_ext_eq _ R (ncompose g (ncompose f x)) (ncompose (fun u => g (f u)) x).
Proof.
  induction n; simpl; intros x HR; auto.
Qed.

Lemma nforall_respects_ext_eq :
  forall n T (P Q : narg n T Prop) (R : Prop -> Prop -> Prop),
    (forall A B, R A B -> (A <-> B)) ->
    narg_ext_eq _ R P Q ->
    nforall n T P <-> nforall n T Q.
Proof.
  induction n; simpl; intros T P Q R HR HPQ.
  - subst. firstorder.
  - split; intros H t; specialize (IHn T (P t) (Q t) R HR (HPQ t)).
    + firstorder.
    + firstorder.
Qed.

Lemma ncompose_respects_ext_eq :
  forall T U V (f g : U -> V) (RU : _ -> _ -> Prop) (RV : _ -> _ -> Prop)  n (A B : narg n T U),
    (forall u1 u2, RU u1 u2 -> RV (f u1) (g u2)) ->
    narg_ext_eq n RU A B ->
    narg_ext_eq n RV (ncompose f A) (ncompose g B).
Proof.
  induction n; simpl; intros A B HR E; auto.
Qed.

Theorem nlist_length : forall n T, nforall n T (ncompose (has_length_n n T) (nlist n T)).
Proof.
  unfold has_length_n.
  intros n T.
  induction n; simpl.
  - reflexivity.
  - intros t.
    eapply nforall_respects_ext_eq with (R := fun A B => A <-> B); [| |apply IHn].
    firstorder.

    eapply narg_ext_eq_trans.
    firstorder.
    apply ncompose_compose.
    firstorder.

    eapply ncompose_respects_ext_eq with (RU := fun l1 l2 => l1 = l2).
    simpl. firstorder. congruence. congruence.

    apply narg_ext_eq_refl.
    auto.
Qed.
Print Assumptions nlist_length.
