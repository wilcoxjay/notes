Require Import List Arith PArith ZArith Ascii Omega Integers.
Import ListNotations.
Set Implicit Arguments.

Module Type SM.
  Parameter t : Type.
  Parameter e : Type.

  Parameter skip   : t.
  Parameter seq    : t -> t -> t.
  Parameter putElt : e -> t.
  (* Parameter putByte : char.t -> t. *)

  (* ghost! *)
  Parameter denote : t -> list e.

  Parameter denote_skip : denote skip = [].
  Parameter denote_seq : forall m1 m2, denote (seq m1 m2) = denote m1 ++ denote m2.
  Parameter denote_putElt : forall b, denote (putElt b) = [b].
  (* Parameter denote_putByte : forall c, denote (putByte c) = char.denote c. *)
End SM.

Module sm : SM with Definition e := bool.
  Definition t := list bool.
  Definition e := bool.
  Definition skip : t := [].
  Definition seq : t -> t -> t := @app _.
  Definition putElt : bool -> t := fun b => [b].
  (* Definition putByte : char.t -> t := char.denote. *)
  Definition denote : t -> list bool := fun x => x.

  Lemma denote_skip : denote skip = [].
  Proof. reflexivity. Qed.

  Lemma denote_seq : forall m1 m2, denote (seq m1 m2) = denote m1 ++ denote m2.
  Proof. reflexivity. Qed.

  Lemma denote_putElt : forall b, denote (putElt b) = [b].
  Proof. reflexivity. Qed.

  (* Lemma denote_putByte : forall c, denote (putByte c) = char.denote c.
  Proof. reflexivity. Qed. *)
End sm.
Hint Rewrite sm.denote_skip sm.denote_seq sm.denote_putElt (*sm.denote_putByte*) : serializer.

Extract Constant sm.t => "Sm.t".
Extract Constant sm.skip => "Sm.skip".
Extract Constant sm.seq => "Sm.seq".
Extract Constant sm.putElt => "Sm.putElt".
Extract Constant sm.denote => "(fun x -> failwith ""sm.denote"")".

Module sm_notations.
  Delimit Scope sm_scope with sm.
  Infix "++" := sm.seq : sm_scope.
  Open Scope sm_scope.
End sm_notations.
Import sm_notations.

Inductive step_result S A :=
| Error
| Success (a : A)
| More (s : S).
Arguments Error {_} {_}.
Arguments Success {_} {_} _.
Arguments More {_} {_} _.

Module Type DM.
  Parameter t : Type -> Type.
  Parameter e : Type.

  Parameter ret : forall {A}, A -> t A.
  Parameter bind   : forall {A B}, t A -> (A -> t B) -> t B.
  Parameter getElt : t e.
  (* Parameter getByte : t char.t. *)

  Parameter fold : forall {S A}, (S -> e -> step_result S A) -> S -> t A.

  (* ghost! *)
  Parameter denote : forall {A}, t A -> list e -> option (A * list e).

  Parameter denote_ret : forall A (a : A) l, denote (ret a) l = Some (a, l).
  Parameter denote_bind : forall A B (m : t A) (f : A -> t B) l,
      denote (bind m f) l = match denote m l with
                            | None => None
                            | Some (a, l) => denote (f a) l
                            end.
  Parameter denote_getElt : forall l,
      denote getElt l = match l with
                        | [] => None
                        | b :: l => Some (b, l)
                        end.
  (*
  Parameter denote_getByte : forall l,
      denote getByte l =
      match l with
      | b1::b2::b3::b4::b5::b6::b7::b8::l =>
        Some (char.undenote [b1; b2; b3; b4; b5; b6; b7; b8], l)
      | _ => None
      end. *)
  Parameter denote_fold : forall S A (f : S -> e -> step_result S A) (s : S) l,
      denote (fold f s) l = match l with
                            | [] => None
                            | b :: l => match f s b with
                                       | Error => None
                                       | Success a => Some (a, l)
                                       | More s => denote (fold f s) l
                                       end
                            end.
End DM.

Module dm : DM with Definition e := bool.
Definition t (A : Type) : Type := list bool -> option (A * list bool).
Definition e := bool.
Definition ret {A} (a : A) : t A := fun l => Some (a, l).
Definition bind {A B} (m : t A) (f : A -> t B) : t B :=
  fun l => match m l with
        | None => None
        | Some (a, l) => f a l
        end.
Definition getElt : t bool :=
  fun l => match l with
        | [] => None
        | b :: l => Some (b, l)
        end.

(*
Definition getByte : t char.t :=
  fun l => match l with
        | b1::b2::b3::b4::b5::b6::b7::b8::l =>
          Some (char.undenote [b1; b2; b3; b4; b5; b6; b7; b8], l)
        | _ => None
        end. *)

Fixpoint fold {S A} (f : S -> bool -> step_result S A) (s : S) (l : list bool) :=
  match l with
  | [] => None
  | b :: l => match f s b with
             | Error => None
             | Success a => Some (a, l)
             | More s => fold f s l
             end
  end.

Definition denote {A} (m : t A) := m.

Lemma denote_ret : forall A (a : A) l, denote (ret a) l = Some (a, l).
Proof. reflexivity. Qed.

Lemma denote_bind : forall A B (m : t A) (f : A -> t B) l,
    denote (bind m f) l = match denote m l with
                          | None => None
                          | Some (a, l) => denote (f a) l
                          end.
Proof. reflexivity. Qed.

Lemma denote_getElt : forall l,
    denote getElt l = match l with
                      | [] => None
                      | b :: l => Some (b, l)
                      end.
Proof. reflexivity. Qed.

(*
Lemma denote_getByte : forall l,
      denote getByte l =
      match l with
      | b1::b2::b3::b4::b5::b6::b7::b8::l =>
        Some (char.undenote [b1; b2; b3; b4; b5; b6; b7; b8], l)
      | _ => None
      end.
Proof. reflexivity. Qed.*)

Lemma denote_fold : forall S A (f : S -> bool -> step_result S A) (s : S) l,
    denote (fold f s) l = match l with
                          | [] => None
                          | b :: l => match f s b with
                                     | Error => None
                                     | Success a => Some (a, l)
                                     | More s => denote (fold f s) l
                                     end
                          end.
Proof. destruct l; auto. Qed.
End dm.
Hint Rewrite dm.denote_ret dm.denote_bind dm.denote_getElt dm.denote_fold
             (* dm.denote_getByte *) : serializer.

Hint Rewrite app_assoc_reverse app_nil_l app_nil_r : serializer.
Hint Rewrite <- app_comm_cons : serializer.

Extract Constant dm.t "'a" => "'a Dm.t".
Extract Constant dm.ret => "Dm.ret".
Extract Constant dm.bind => "Dm.bind".
Extract Constant dm.getElt => "Dm.getElt".
Extract Constant dm.fold => "Dm.fold".
Extract Constant dm.denote => "(fun x -> failwith ""dm.denote"")".

Module dm_ext.
  Import dm.
  Definition fmap {A B} (f : A -> B) (x : t A) : t B :=
    bind x (fun a => ret (f a)).

  Definition sequence {A B} (df : t (A -> B)) (da : t A) : t B :=
    bind df (fun f => (bind da (fun a => ret (f a)))).
End dm_ext.
Hint Unfold dm_ext.fmap dm_ext.sequence : serializer.

Module dm_notations.
  Delimit Scope dm_scope with dm.
  Notation "m >>= f" := (@dm.bind _ _ m f) (at level 42, left associativity) : dm_scope.

  Notation "x <- c1 ;; c2" := (c1 >>= (fun x => c2))%dm
                                (at level 100, c1 at next level, right associativity) : dm_scope.
  Notation "e1 ;; e2" := (_ <- e1 ;; e2)%dm
                            (at level 100, right associativity) : dm_scope.

  Notation "f <$> x" := (@dm_ext.fmap _ _ f x) (at level 42, left associativity) : dm_scope.

  Notation "f <*> x" := (@dm_ext.sequence _ _ f x) (at level 42, left associativity) : dm_scope.

  Open Scope dm.
End dm_notations.
Import dm_notations.

Notation serializer_spec_ty s d :=
  (forall a l, dm.denote d (sm.denote (s a) ++ l) = Some (a, l)).

Class serializer (A : Type) := Serializer {
  serialize : A -> sm.t;
  deserialize : dm.t A;

  serializer_spec : serializer_spec_ty serialize deserialize
}.
Hint Rewrite @serializer_spec : serializer.

Section lift.
  Context {A B C D : Type}.
  Context {sA : serializer A}.
  Context {sB : serializer B}.
  Context {sC : serializer C}.
  Context {sD : serializer D}.

  Definition liftD1 {X} (f : D -> X) : dm.t X :=
    f <$> deserialize.

  Definition liftD2 {X} (f : C -> D -> X) : dm.t X :=
    (f <$> deserialize) >>= liftD1.

  Definition liftD3 {X} (f : B -> C -> D -> X) : dm.t X :=
    (f <$> deserialize) >>= liftD2.

  Definition liftD4 {X} (f : A -> B -> C -> D -> X) : dm.t X :=
    (f <$> deserialize) >>= liftD3.
End lift.
Hint Unfold liftD1 liftD2 liftD3 liftD4 : serializer.

Instance BoolSerializer : serializer bool := @Serializer _ sm.putElt dm.getElt _.
- intros. autorewrite with serializer. reflexivity.
Defined.


Fixpoint positive_serialize (p : positive) : sm.t :=
  match p with
  | xI p => serialize true ++ serialize true ++ positive_serialize p
  | xO p => serialize true ++ serialize false ++ positive_serialize p
  | xH => serialize false
  end.

Module positive_deserialize.
Inductive state :=
| Start (k : positive -> positive)
| OneMoreElt (k : positive -> positive).

Definition step (s : state) (b : bool) : step_result _ _ :=
  match s with
  | Start k => if b then More (OneMoreElt k) else Success (k xH)
  | OneMoreElt k => More (Start (fun p => k ((if b then xI else xO) p)))
  end.

Definition f : dm.t positive :=
  dm.fold step (Start (fun x => x)).
End positive_deserialize.

Lemma spec_pos' :
  forall p k l,
    dm.denote (dm.fold positive_deserialize.step (positive_deserialize.Start k))
              (sm.denote (positive_serialize p) ++ l) = Some (k p, l).
Proof.
  induction p; simpl; intros.
  - now autorewrite with serializer using (simpl; try rewrite IHp).
  - now autorewrite with serializer using (simpl; try rewrite IHp).
  - now autorewrite with serializer.
Qed.

Lemma spec_pos : serializer_spec_ty positive_serialize positive_deserialize.f.
Proof.
  intros p l.
  unfold positive_deserialize.f.
  apply spec_pos'.
Qed.

Instance positive_serializer :
  serializer positive := @Serializer _ positive_serialize positive_deserialize.f spec_pos.

Definition Z_serialize (z : Z) : sm.t :=
  match z with
  | Z0 => serialize false
  | Zpos p => serialize true ++ serialize true ++ serialize p
  | Zneg p => serialize true ++ serialize false ++ serialize p
  end.

Definition Z_deserialize : dm.t Z :=
  tag <- deserialize ;;
  match tag with
  | true => sign <- deserialize ;;
           (match sign with true => Zpos | false => Zneg end) <$> deserialize
  | false => dm.ret Z0
  end.

Ltac serializer_spec_crush :=
  intros; autounfold with serializer; autorewrite with serializer; auto.

Lemma Z_serializer_spec :
  serializer_spec_ty Z_serialize Z_deserialize.
Proof.
  unfold Z_serialize, Z_deserialize.
  destruct a; serializer_spec_crush.
Qed.

Instance Z_serializer : serializer Z :=
  {| serialize := Z_serialize;
     deserialize := Z_deserialize;
     serializer_spec := Z_serializer_spec
  |}.

Definition N_serialize (n : N) :=
  match n with
  | N0 => serialize false
  | Npos p => serialize true ++ serialize p
  end.

Definition N_deserialize :=
  tag <- deserialize ;;
  match tag with
  | false => dm.ret N0
  | true => Npos <$> deserialize
  end.

Lemma N_serializer_spec :
  serializer_spec_ty N_serialize N_deserialize.
Proof.
  unfold N_serialize, N_deserialize.
  destruct a; serializer_spec_crush.
Qed.

Instance N_serializer : serializer N :=
  {| serialize := N_serialize;
     deserialize := N_deserialize;
     serializer_spec := N_serializer_spec
  |}.

Definition nat_serialize (n : nat) := serialize (N.of_nat n).

Definition nat_deserialize := N.to_nat <$> deserialize.

Lemma nat_serializer_spec :
  serializer_spec_ty nat_serialize nat_deserialize.
Proof.
  unfold nat_serialize, nat_deserialize.
  serializer_spec_crush.
  now rewrite Nnat.Nat2N.id.
Qed.

Instance nat_serializer : serializer nat :=
  {| serialize := nat_serialize;
     deserialize := nat_deserialize;
     serializer_spec := nat_serializer_spec
  |}.


Arguments Some {_} _.
Arguments cons {_} _ _.


Section combinators.
  (* This section gives instances for various type constructors, including pairs
    and lists. *)
  Variables A B : Type.
  Variable sA : serializer A.
  Variable sB : serializer B.

  Definition option_serialize (x : option A) :=
    match x with
    | Some a => serialize true ++ serialize a
    | None => serialize false
    end.

  Definition option_deserialize : dm.t (option A) :=
    b <- deserialize ;;
    match b with
    | true => Some <$> deserialize
    | false => dm.ret None
    end.

  Lemma option_serializer_spec :
    serializer_spec_ty option_serialize option_deserialize.
  Proof.
    unfold option_serialize, option_deserialize.
    destruct a; serializer_spec_crush.
  Qed.

  Global Instance option_serializer : serializer (option A) :=
    {| serialize := option_serialize;
        deserialize := option_deserialize;
        serializer_spec := option_serializer_spec
    |}.


  Definition pair_serialize (x : A * B) :=
    let (a, b) := x in serialize a ++ serialize b.

  Definition pair_deserialize : dm.t (A * B) :=
    liftD2 pair.

  Lemma pair_serializer_spec :
    serializer_spec_ty pair_serialize pair_deserialize.
  Proof.
    unfold pair_serialize, pair_deserialize.
    destruct a; serializer_spec_crush.
  Qed.

  Global Instance pair_serializer : serializer (A * B) :=
    {| serialize := pair_serialize;
        deserialize := pair_deserialize;
        serializer_spec := pair_serializer_spec
    |}.


  Definition sum_serialize (x : A + B) :=
    match x with
    | inl a => serialize true ++ serialize a
    | inr b => serialize false ++ serialize b
    end.

  Definition sum_deserialize : dm.t (A + B) :=
    b <- deserialize ;;
    match b with
    | true => inl <$> deserialize
    | false => inr <$> deserialize
    end.

  Lemma sum_serializer_spec :
    serializer_spec_ty sum_serialize sum_deserialize.
  Proof.
    unfold sum_serialize, sum_deserialize.
    destruct a; serializer_spec_crush.
  Qed.

  Global Instance sum_serializer : serializer (A + B) :=
    {| serialize := sum_serialize;
        deserialize := sum_deserialize;
        serializer_spec := sum_serializer_spec
    |}.


  Fixpoint list_serialize_rec (l : list A) : sm.t :=
    match l with
    | [] => sm.skip
    | a :: l' => serialize a ++ list_serialize_rec l'
    end.

  Definition list_serialize (l : list A) : sm.t :=
    serialize (length l) ++ list_serialize_rec l.

  Fixpoint list_deserialize_rec (n : nat) : dm.t (list A) :=
    match n with
    | 0 => dm.ret []
    | S n' => cons <$> deserialize <*> list_deserialize_rec n'
    end.

  Definition list_deserialize : dm.t (list A) :=
    deserialize >>= list_deserialize_rec.

  Lemma list_serializer_spec_rec :
    forall l bin, dm.denote (list_deserialize_rec (length l))
                       (sm.denote (list_serialize_rec l) ++ bin) = Some (l, bin).
  Proof.
    induction l; simpl; serializer_spec_crush.
    rewrite IHl.
    serializer_spec_crush.
  Qed.

  Lemma list_serializer_spec :
    serializer_spec_ty list_serialize list_deserialize.
  Proof.
    unfold list_serialize, list_deserialize.
    serializer_spec_crush.
    apply list_serializer_spec_rec.
  Qed.

  Global Instance list_serializer : serializer (list A) :=
    {| serialize := list_serialize;
        deserialize := list_deserialize;
        serializer_spec := list_serializer_spec
    |}.
End combinators.

Require Import ExtrOcamlBasic.
Extraction Inline positive_serializer Z_serializer N_serializer nat_serializer option_serializer pair_serializer sum_serializer list_serializer.
Set Extraction Optimize.

Recursive Extraction list_serializer.
