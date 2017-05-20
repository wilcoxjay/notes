Require Import List Arith PArith ZArith Ascii Omega Integers.
Import ListNotations.
Set Implicit Arguments.

Inductive step_result S A :=
| Error
| Success (a : A)
| More (s : S).
Arguments Error {_} {_}.
Arguments Success {_} {_} _.
Arguments More {_} {_} _.

Module dmachine.
  Record t (E A : Type) : Type := Make {
    state : Type;
    init : state;
    step : state -> E -> step_result state A
  }.


  Definition run {E S A} (step : S -> E -> step_result S A) : S -> list E -> option (A * list E) :=
    fix go (s : S) (l : list E) {struct l} : option (A * list E) :=
    match l with
    | [] => None
    | e :: l =>
      match step s e with
      | Error => None
      | Success a => Some (a, l)
      | More s => go s l
      end
    end.
End dmachine.

Module serializer.
  Class t (E A : Type) : Type := Make {
    serialize : A -> list E;
    dmachine : dmachine.t E A;
    spec : forall a l, dmachine.run (dmachine.step dmachine)
                               (dmachine.init dmachine)
                               (serialize a ++ l)
                  = Some (a, l)
  }.

  Section lemmas.
    Variables (E A : Type).
    Context {sA : t E A}.

    Lemma spec' : forall a,
        dmachine.run (dmachine.step dmachine)
                     (dmachine.init dmachine)
                     (serialize a)
        = Some (a, []).
    Proof.
      intros.
      rewrite <- app_nil_r with (l := serialize a) at 1.
      now rewrite serializer.spec.
    Qed.
  End lemmas.

  Module exports.
    Definition serialize {E A t} := @serialize E A t.
  End exports.
End serializer.
Import serializer.exports.

Definition bool_serialize (b : bool) := [b].

Definition bool_dmachine : dmachine.t bool bool :=
  dmachine.Make tt (fun _ b => Success b).

Instance bool_serializer : serializer.t bool bool :=
  serializer.Make bool_serialize bool_dmachine _.
Proof.
  now destruct a; simpl; intros.
Defined.

Fixpoint positive_serialize (p : positive) : list bool :=
  match p with
  | xI p => serialize true ++ serialize true ++ positive_serialize p
  | xO p => serialize true ++ serialize false ++ positive_serialize p
  | xH => serialize false
  end.

Module positive_dmachine.
  Inductive state :=
  | Start (k : positive -> positive)
  | OneMoreElt (k : positive -> positive).

  Definition step (s : state) (b : bool) : step_result _ _ :=
    match s with
    | Start k => if b then More (OneMoreElt k) else Success (k xH)
    | OneMoreElt k => More (Start (fun p => k ((if b then xI else xO) p)))
    end.

  Definition init := (Start (fun x => x)).

  Definition m := dmachine.Make init step .
End positive_dmachine.

Lemma positive_run_k :
  forall p k l,
    dmachine.run positive_dmachine.step
                 (positive_dmachine.Start k)
                 (positive_serialize p ++ l)
    = Some (k p, l).
Proof.
  induction p; simpl; intros.
  - apply IHp.
  - apply IHp.
  - reflexivity.
Qed.

Lemma positive_run : forall p l,
    dmachine.run positive_dmachine.step (positive_dmachine.Start (fun x => x))
                 (positive_serialize p ++ l) = Some (p, l).
Proof.
  intros.
  apply positive_run_k.
Qed.

Instance positive_serializer : serializer.t bool positive :=
  serializer.Make positive_serialize positive_dmachine.m positive_run.

Section convert.
  Variable E A B : Type.
  Context {sA : serializer.t E A}.

  Variable A_to_B : A -> B.
  Variable B_to_A : B -> A.

  Hypothesis AB_inv : forall b, A_to_B (B_to_A b) = b.

  Notation machine s := (@serializer.dmachine _ _ s).
  Notation state m := (dmachine.state m).
  Notation step m := (dmachine.step m).
  Notation init m := (dmachine.init m).

  Definition convert_serialize (b : B) : list E :=
    serialize (B_to_A b).

  Definition convert_step (s : state (machine sA)) (e : E) : step_result (state (machine sA)) B :=
    match step (machine sA) s e with
    | Error => Error
    | Success a => Success (A_to_B a)
    | More s => More s
    end.

  Definition convert_dmachine : dmachine.t E B :=
    dmachine.Make (init (machine sA)) convert_step.

  Lemma convert_run :
    forall l s,
      dmachine.run convert_step s l =
      match dmachine.run (step (machine sA)) s l with
      | None => None
      | Some (a, l) => Some (A_to_B a, l)
      end.
  Proof.
    unfold convert_step.
    induction l; simpl; intros; auto.
    destruct (step _); auto.
  Qed.

  Instance convert_serializer : serializer.t E B :=
    serializer.Make convert_serialize convert_dmachine _.
  Proof.
    intros b l.
    simpl.
    unfold convert_serialize.
    now rewrite convert_run, serializer.spec, AB_inv.
  Defined.
End convert.

Definition N_serialize (n : N) : list bool :=
  match n with
  | N0 => serialize false
  | Npos p => serialize true ++ serialize p
  end.

Module N_dmachine.

Inductive state : Type :=
| Start
| Pos : positive_dmachine.state -> state.

Definition step (s : state) (b : bool) : step_result state N :=
  match s with
  | Start =>
    if b
    then More (Pos positive_dmachine.init)
    else Success N0
  | Pos s =>
    match positive_dmachine.step s b with
    | Error => Error
    | Success p => Success (Npos p)
    | More s => More (Pos s)
    end
  end.

Definition init := Start.

Definition m := dmachine.Make init step.
End N_dmachine.


Lemma N_run_pos :
  forall l s,
    dmachine.run N_dmachine.step (N_dmachine.Pos s) l =
    match dmachine.run positive_dmachine.step s l with
    | None => None
    | Some (p, l) => Some (Npos p, l)
    end.
Proof.
  induction l; simpl; intros.
  - auto.
  - destruct positive_dmachine.step; auto.
Qed.

Instance N_serializer : serializer.t bool N :=
  serializer.Make N_serialize N_dmachine.m _.
intros n l.
destruct n; simpl.
- auto.
- now rewrite N_run_pos, (serializer.spec(t := positive_serializer)).
Defined.

Instance nat_serializer : serializer.t bool nat :=
  convert_serializer N.to_nat N.of_nat Nnat.Nat2N.id.

Section dmachine_combinators.
  Variable A B : Type.
  Context {sA : serializer.t bool A}.
  Context {sB : serializer.t bool B}.

  Definition pair_serialize (p : A * B) : list bool :=
    let (a, b) := p
    in serialize a ++ serialize b.

  Notation machine s := (@serializer.dmachine _ _ s).
  Notation state m := (dmachine.state m).
  Notation step m := (dmachine.step m).
  Notation init m := (dmachine.init m).

  Inductive pair_state : Type :=
  | PS_A : state (machine sA) -> pair_state
  | PS_B : A -> state (machine sB) -> pair_state.

  Definition pair_init : pair_state := PS_A (init (machine sA)).

  Definition pair_step (s : pair_state) (b : bool) : step_result pair_state (A * B) :=
    match s with
    | PS_A sa =>
      match step (machine sA) sa b with
      | Error => Error
      | Success a => More (PS_B a (init (machine sB)))
      | More sa => More (PS_A sa)
      end
    | PS_B a sb =>
      match step (machine sB) sb b with
      | Error => Error
      | Success b => Success (a, b)
      | More sb => More (PS_B a sb)
      end
    end.

  Definition pair_dmachine : dmachine.t bool (A * B) :=
    dmachine.Make pair_init pair_step.

  Lemma run_pair_B :
    forall l a sb,
      dmachine.run pair_step (PS_B a sb) l =
      match dmachine.run (step (machine sB)) sb l with
      | None => None
      | Some (b, l) => Some ((a, b), l)
      end.
  Proof.
    induction l; simpl; intros; auto.
    destruct (step _); auto.
  Qed.

  Lemma run_pair :
    forall l sa,
      dmachine.run pair_step (PS_A sa) l =
      match dmachine.run (step (machine sA)) sa l with
      | None => None
      | Some (a, l) =>
        match dmachine.run (step (machine sB)) (init (machine sB)) l with
        | None => None
        | Some (b, l) => Some ((a, b), l)
        end
      end.
  Proof.
    induction l; simpl; intros; auto.
    destruct (step _); auto using run_pair_B.
  Qed.

  Instance pair_serializer : serializer.t bool (A * B) :=
    serializer.Make pair_serialize pair_dmachine _.
  destruct a as [a b].
  intros.
  simpl.
  unfold pair_init.
  now rewrite run_pair, app_assoc_reverse, !serializer.spec.
  Defined.


  Fixpoint list_serialize_rec (l : list A) : list bool :=
    match l with
    | [] => []
    | a :: l => serialize a ++ list_serialize_rec l
    end.

  Definition list_serialize (l : list A) : list bool :=
    serialize (length l) ++ list_serialize_rec l.

  Inductive list_state :=
  | LS_length (s : state (machine nat_serializer))
  | LS_elts (n : nat) (l : list A) (s : state (machine sA)).

  Definition list_init := LS_length (init (machine nat_serializer)).

  Definition list_step (s : list_state) (b : bool) : step_result list_state (list A) :=
    match s with
    | LS_length s =>
      match step (machine nat_serializer) s b with
      | Error => Error
      | Success n =>
        match n with
        | 0 => Success []
        | S n => More (LS_elts n [] (init (machine sA)))
        end
      | More s => More (LS_length s)
      end
    | LS_elts n l s =>
      match step (machine sA) s b with
      | Error => Error
      | Success a =>
        match n with
        | 0 => Success (List.rev (a :: l))
        | S n => More (LS_elts n (a :: l) (init (machine sA)))
        end
      | More s => More (LS_elts n l s)
      end
    end.

  Definition list_dmachine :=
    dmachine.Make list_init list_step.

  Lemma list_step_length :
    forall l s,
      dmachine.run list_step (LS_length s) l =
      match dmachine.run (step (machine nat_serializer)) s l with
      | None => None
      | Some (n, l) =>
        match n with
        | 0 => Some ([], l)
        | S n =>
          dmachine.run list_step (LS_elts n [] (init (machine sA))) l
        end
      end.
  Proof.
    induction l; simpl; intros; auto.
    destruct convert_step; auto.
    destruct a0; auto.
  Qed.

  Lemma list_step_elts :
    forall l n acc s,
      dmachine.run list_step (LS_elts n acc s) l =
      match dmachine.run (step (machine sA)) s l with
      | None => None
      | Some (a, l) =>
        match n with
        | 0 => Some (List.rev (a :: acc), l)
        | S n => dmachine.run list_step (LS_elts n (a :: acc) (init (machine sA))) l
        end
      end.
  Proof.
    induction l; simpl; intros; auto.
    destruct (step _); eauto.
    destruct n; auto.
  Qed.

  Lemma list_serialize_rec_spec :
    forall l bin n acc,
      S n = length l ->
      dmachine.run (step list_dmachine) (LS_elts n acc (init (machine sA)))
                   (list_serialize_rec l ++ bin) =
      Some (rev_append acc l, bin)%list.
  Proof.
    induction l; simpl; intros.
    - congruence.
    - rewrite list_step_elts, app_assoc_reverse, serializer.spec.
      destruct n.
      + destruct l.
        * now rewrite rev_append_rev.
        * simpl in *. congruence.
      + now rewrite IHl by congruence.
  Qed.

  Instance list_serializer : serializer.t bool (list A) :=
    serializer.Make list_serialize list_dmachine _.
  Proof.
    intros l bin.
    cbn [init list_dmachine].
    unfold list_init, list_serialize.
    rewrite list_step_length, app_assoc_reverse, serializer.spec.
    destruct l; auto.
    cbn [length].
    now rewrite list_serialize_rec_spec.
  Defined.
End dmachine_combinators.

Section pair_elements.
  Variable E A : Type.
  Context {sA : serializer.t (E * E) A}.

  Notation m := (serializer.dmachine(t:=sA)).

  Definition concat_pairs l :=
    concat (map (fun (p : E * E) => let (x, y) := p in [x; y]) l).

  Definition pair_element_serialize (a : A) : list E :=
    concat_pairs (serializer.serialize a).

  Inductive pair_element_state : Type :=
  | PE_even (s : dmachine.state m)
  | PE_odd (e : E) (s : dmachine.state m).

  Definition pair_element_init := PE_even (dmachine.init m).

  Definition pair_element_step (s : pair_element_state) (e : E)
    : step_result pair_element_state A :=
    match s with
    | PE_even s => More (PE_odd e s)
    | PE_odd e1 s =>
      match dmachine.step m s (e1, e) with
      | Error => Error
      | Success a => Success a
      | More s => More (PE_even s)
      end
    end.

  Definition pair_element_dmachine :=
    dmachine.Make pair_element_init pair_element_step.

  Lemma pair_element_step_even :
    forall l s bin,
      dmachine.run pair_element_step (PE_even s) (concat_pairs l ++ bin) =
      match dmachine.run (dmachine.step m) s l with
      | None => dmachine.run pair_element_step (PE_even s) (concat_pairs l ++ bin)
      | Some (a, l) =>
        Some (a, concat_pairs l ++ bin)%list
      end.
  Proof.
    induction l; simpl; intros.
    - auto.
    - destruct a as [e1 e2]. simpl.
      destruct dmachine.step; auto.
  Qed.

  Instance pair_element_serializer : serializer.t E A :=
    serializer.Make pair_element_serialize pair_element_dmachine _.
  Proof.
    intros.
    simpl.
    unfold pair_element_serialize, pair_element_init.
    now rewrite pair_element_step_even, serializer.spec'.
  Defined.
End pair_elements.

