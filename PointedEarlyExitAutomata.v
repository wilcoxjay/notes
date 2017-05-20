Require Import List Arith PArith ZArith Ascii Omega Integers.
Import ListNotations.
Set Implicit Arguments.

Inductive step_result S A :=
| Success (a : A)
| More (s : S).
Arguments Success {_} {_} _.
Arguments More {_} {_} _.

Module automaton.
  Notation step_t E S A := (S -> E -> step_result S A).
  Record t (E S A : Type) : Type := Make {
    init : S;
    step : step_t E S A
  }.

  Definition run' {E S A} (step : step_t E S A) :
      S -> list E -> step_result S (A * list E) :=
    fix go (s : S) (l : list E) : step_result S (A * list E) :=
    match l with
    | [] => More s
    | e :: l =>
      match step s e with
      | Success x => Success (x, l)
      | More s => go s l
      end
    end.

  Lemma run'_app : forall E S A (step : step_t E S A) l1 l2 s,
      run' step s (l1 ++ l2) =
      match run' step s l1 with
      | Success (x, l) => Success (x, l ++ l2)
      | More s => run' step s l2
      end.
  Proof.
    induction l1; simpl; intros.
    - auto.
    - destruct step0; auto.
  Qed.

  Definition run {E S A} (a : t E S A) := (run' (step a) (init a)).

  Definition one_step {E} : step_t E unit E :=
    fun _ => Success.

  Definition one_init : unit := tt.

  Definition one {E} : t E unit E := Make one_init one_step.

  Lemma run'_one_step : forall E u (l : list E),
      run' one_step u l =
      match l with
      | [] => More u
      | x :: l => Success (x, l)
      end.
  Proof. destruct l; reflexivity. Qed.

  Lemma run_one : forall E (l : list E),
      run one l =
      match l with
      | [] => More tt
      | x :: l => Success (x, l)
      end.
  Proof.
    unfold run.
    intros.
    now rewrite run'_one_step.
  Qed.


  Definition map_step {E S A B} (f : A -> B) (a : step_t E S A) : step_t E S B :=
    fun s e =>
      match a s e with
      | Success x => Success (f x)
      | More s => More s
      end.

  Definition map {E S A B} (f : A -> B) (a : t E S A) : t E S B :=
    Make (init a) (map_step f (step a)).

  Lemma run'_map_step : forall E S A B (f : A -> B) (a : step_t E S A) l s,
      run' (map_step f a) s l =
      match run' a s l with
      | Success (x, l) => Success (f x, l)
      | More s => More s
      end.
  Proof.
    unfold map_step.
    induction l; simpl; intros.
    - auto.
    - destruct a; auto.
  Qed.

  Lemma run_map : forall E S A B (f : A -> B) (a : t E S A) l,
      run (map f a) l =
      match run a l with
      | Success (x, l) => Success (f x, l)
      | More s => More s
      end.
  Proof.
    unfold run.
    intros.
    simpl.
    now rewrite run'_map_step.
  Qed.

  Definition pair_step {E S1 A S2 B} (a : step_t E S1 A) (b : step_t E S2 B) :
      step_t E (S1 * S2 + A * S2) (A * B) :=
    fun s e =>
      match s with
      | inl (s1, s2) =>
        match a s1 e with
        | Success x => More (inr (x, s2))
        | More s1 => More (inl (s1, s2))
        end
      | inr (x, s2) =>
        match b s2 e with
        | Success b => Success (x, b)
        | More s2 => More (inr (x, s2))
        end
      end.

  Definition pair {E S1 A S2 B} (a : t E S1 A) (b : t E S2 B) :
      t E (S1 * S2 + A * S2) (A * B) :=
    Make (inl (init a, init b)) (pair_step (step a) (step b)).

  Lemma run'_pair_step_inr : forall E S1 A S2 B (a : step_t E S1 A) (b : step_t E S2 B) x l s,
      run' (pair_step a b) (inr (x, s)) l =
      match run' b s l with
      | Success (y, l) => Success ((x, y), l)
      | More s => More (inr (x, s))
      end.
  Proof.
    induction l; simpl; intros.
    - auto.
    - destruct b; auto.
  Qed.

  Lemma run'_pair_step_inl : forall E S1 A S2 B (a : step_t E S1 A) (b : step_t E S2 B) l s1 s2,
      run' (pair_step a b) (inl (s1, s2)) l =
      match run' a s1 l with
      | Success (x, l) => run' (pair_step a b) (inr (x, s2)) l
      | More s1 => More (inl (s1, s2))
      end.
  Proof.
    induction l; simpl; intros.
    - auto.
    - destruct a; auto.
  Qed.

  Lemma run'_pair_step : forall E S1 A S2 B (a : step_t E S1 A) (b : step_t E S2 B) l s1 s2,
      run' (pair_step a b) (inl (s1, s2)) l =
      match run' a s1 l with
      | Success (x, l) =>
        match run' b s2 l with
        | Success (y, l) => Success ((x, y), l)
        | More s => More (inr (x, s))
        end
      | More s1 => More (inl (s1, s2))
      end.
  Proof.
    intros.
    rewrite run'_pair_step_inl.
    destruct run'; auto.
    destruct a0.
    now rewrite run'_pair_step_inr.
  Qed.

  Lemma run_pair : forall E S1 A S2 B (a : t E S1 A) (b : t E S2 B) l,
      run (pair a b) l =
      match run a l with
      | Success (x, l) =>
        match run b l with
        | Success (y, l) => Success ((x, y), l)
        | More s => More (inr (x, s))
        end
      | More s1 => More (inl (s1, init b))
      end.
  Proof.
    unfold run.
    intros.
    apply run'_pair_step.
  Qed.

  Definition lift2_step {E S1 A S2 B C} (f : A -> B -> C) (a : step_t E S1 A) (b : step_t E S2 B) : step_t E _ C :=
    map_step (fun p : A * B => let (a, b) := p in f a b) (pair_step a b).

  Definition lift2 {E S1 A S2 B C} (f : A -> B -> C) (a : t E S1 A) (b : t E S2 B) : t E _ C :=
    Make (inl (init a, init b)) (lift2_step f (step a) (step b)).

  Lemma run'_lift2_step_inl : forall E S1 A S2 B C (f : A -> B -> C) (a : step_t E S1 A) (b : step_t E S2 B) l s1 s2,
      run' (lift2_step f a b) (inl (s1, s2)) l =
      match run' a s1 l with
      | Success (x, l) => run' (lift2_step f a b) (inr (x, s2)) l
      | More s1 => More (inl (s1, s2))
      end.
  Proof.
    intros.
    unfold lift2_step.
    rewrite run'_map_step, run'_pair_step_inl.
    destruct run'; auto.
    destruct a0.
    rewrite run'_map_step; auto.
  Qed.

  Lemma run'_lift2_step_inr : forall E S1 A S2 B C (f : A -> B -> C) (a : step_t E S1 A) (b : step_t E S2 B) l x s,
      run' (lift2_step f a b) (inr (x, s)) l =
      match run' b s l with
      | Success (y, l) => Success (f x y, l)
      | More s => More (inr (x, s))
      end.
  Proof.
    intros.
    unfold lift2_step.
    rewrite run'_map_step, run'_pair_step_inr.
    destruct run'; auto.
    destruct a0; auto.
  Qed.

  Lemma run'_lift2_step : forall E S1 A S2 B C (f : A -> B -> C) (a : step_t E S1 A) (b : step_t E S2 B) l s1 s2,
      run' (lift2_step f a b) (inl (s1, s2)) l =
      match run' a s1 l with
      | Success (x, l) =>
        match run' b s2 l with
        | Success (y, l) => Success (f x y, l)
        | More s2 => More (inr (x, s2))
        end
      | More s1 => More (inl (s1, s2))
      end.
  Proof.
    intros.
    rewrite run'_lift2_step_inl.
    destruct run'; auto.
    destruct a0.
    rewrite run'_lift2_step_inr. auto.
  Qed.

  Lemma run_lift2 : forall E S1 A S2 B C (f : A -> B -> C) (a : t E S1 A) (b : t E S2 B) l,
      run (lift2 f a b) l =
      match run a l with
      | Success (x, l) =>
        match run b l with
        | Success (y, l) => Success (f x y, l)
        | More s2 => More (inr (x, s2))
        end
      | More s1 => More (inl (s1, init b))
      end.
  Proof.
    unfold run.
    intros.
    simpl.
    now rewrite run'_lift2_step.
  Qed.

  Definition bind_step {E S1 A S2 B} (a : step_t E S1 A) (init : A -> S2) (b : A -> step_t E S2 B) : step_t E _ B :=
    fun s e =>
      match s with
      | inl s1 =>
        match a s1 e with
        | Success x => More (inr (x, init x))
        | More s1 => More (inl s1)
        end
      | inr (x, s2) =>
        match b x s2 e with
        | Success y => Success y
        | More s2 => More (inr (x, s2))
        end
      end.

  Definition bind {E S1 A S2 B} (a : t E S1 A) (b : A -> t E S2 B) : t E _ B :=
    Make (inl (init a)) (bind_step (step a) (fun x => init (b x)) (fun x => step (b x))).

End automaton.

Definition bool_step : automaton.t bool unit bool := automaton.one.

