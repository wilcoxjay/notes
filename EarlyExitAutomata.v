Require Import List Arith PArith ZArith Ascii Omega Integers.
Import ListNotations.
Set Implicit Arguments.

Inductive step_result S A :=
| Success (a : A)
| More (s : S).
Arguments Success {_} {_} _.
Arguments More {_} {_} _.


Module automaton.
  Definition t (E S A : Type) : Type :=
    S -> E -> step_result S A.

  Definition run {E S A} (a : t E S A) : S -> list E -> step_result S (A * list E) :=
    fix go (s : S) (l : list E) : step_result S (A * list E) :=
    match l with
    | [] => More s
    | e :: l =>
      match a s e with
      | Success x => Success (x, l)
      | More s => go s l
      end
    end.

  Definition one {E} : t E unit E :=
    fun _ => Success.

  Lemma run_one : forall E u (l : list E),
      run one u l = match l with
                    | [] => More u
                    | x :: l => Success (x, l)
                    end.
  Proof. destruct l; reflexivity. Qed.

  Definition arr {E S A} (f : S -> E -> A) : t E S A :=
    fun s e => Success (f s e).

  Lemma run_arr : forall E S A (f : S -> E -> A) l s,
      run (arr f) s l = match l with
                        | [] => More s
                        | e :: l => Success (f s e, l)
                        end.
  Proof. destruct l; reflexivity. Qed.

  Definition first {E S A B} (a : t E S A) : t E (S * B) (A * B) :=
    fun p e =>
      let '(s, b) := p in
      match a s e with
      | Success x => Success (x, b)
      | More s => More (s, b)
      end.

  Lemma run_first : forall E S A B (a : t E S A) (b : B) l s,
      run (first a) (s, b) l =
      match run a s l with
      | Success (x, l) => Success ((x, b), l)
      | More s => More (s, b)
      end.
  Proof.
    induction l; simpl; intros.
    - auto.
    - destruct a; auto.
  Qed.

  Definition map {E S A B} (f : A -> B) (a : t E S A) : t E S B :=
    fun s e =>
      match a s e with
      | Success x => Success (f x)
      | More s => More s
      end.

  Lemma run_map : forall E S A B (f : A -> B) (a : t E S A) l s,
      run (map f a) s l =
      match run a s l with
      | Success (x, l) => Success (f x, l)
      | More s => More s
      end.
  Proof.
    unfold map.
    induction l; simpl; intros.
    - auto.
    - destruct a; auto.
  Qed.

  Definition pair {E S1 A S2 B} (a : t E S1 A) (b : t E S2 B) : t E (S1 * S2 + A * S2) (A * B) :=
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

  Lemma run_pair_inr : forall E S1 A S2 B (a : t E S1 A) (b : t E S2 B) x l s,
      run (pair a b) (inr (x, s)) l =
      match run b s l with
      | Success (y, l) => Success ((x, y), l)
      | More s => More (inr (x, s))
      end.
  Proof.
    induction l; simpl; intros.
    - auto.
    - destruct b; auto.
  Qed.

  Lemma run_pair_inl : forall E S1 A S2 B (a : t E S1 A) (b : t E S2 B) l s1 s2,
      run (pair a b) (inl (s1, s2)) l =
      match run a s1 l with
      | Success (x, l) => run (pair a b) (inr (x, s2)) l
      | More s1 => More (inl (s1, s2))
      end.
  Proof.
    induction l; simpl; intros.
    - auto.
    - destruct a; auto.
  Qed.

  Definition sequence {E S1 A S2 B} (a : t E S1 A) (b : t E S2 B) : t E (S1 * (A -> S2) + S2) B :=
    fun s e =>
      match s with
      | inl (s1, s2) =>
        match a s1 e with
        | Success x => More (inr (s2 x))
        | More s1 => More (inl (s1, s2))
        end
      | inr s2 =>
        match b s2 e with
        | Success b => Success b
        | More s2 => More (inr s2)
        end
      end.

  Lemma run_sequence_inl : forall E S1 A S2 B (a : t E S1 A) (b : t E S2 B) f l s,
      run (sequence a b) (inl (s, f)) l =
      match run a s l with
      | Success (x, l) => run (sequence a b) (inr (f x)) l
      | More s => More (inl (s, f))
      end.
  Proof.
    induction l; simpl; intros.
    - auto.
    - destruct a; auto.
  Qed.

  Lemma run_sequence_inr : forall E S1 A S2 B (a : t E S1 A) (b : t E S2 B) l s,
      run (sequence a b) (inr s) l =
      match run b s l with
      | Success y => Success y
      | More s => More (inr s)
      end.
  Proof.
    induction l; simpl; intros.
    - auto.
    - destruct b; auto.
  Qed.

  Definition choice {E S1 S2 A B} (a : t E S1 A) (b : t E S2 B) : t E (S1 + S2) (A + B) :=
    fun s e =>
      match s with
      | inl s =>
        match a s e with
        | Success a => Success (inl a)
        | More s => More (inl s)
        end
      | inr s =>
        match b s e with
        | Success b => Success (inr b)
        | More s => More (inr s)
        end
      end.

  Lemma run_choice_inl : forall E S1 S2 A B (a : t E S1 A) (b : t E S2 B) l s,
      run (choice a b) (inl s) l =
      match run a s l with
      | Success (y, l) => Success (inl y, l)
      | More s => More (inl s)
      end.
  Proof.
    induction l; simpl; intros.
    - auto.
    - destruct a; auto.
  Qed.

  Lemma run_choice_inr : forall E S1 S2 A B (a : t E S1 A) (b : t E S2 B) l s,
      run (choice a b) (inr s) l =
      match run b s l with
      | Success (y, l) => Success (inr y, l)
      | More s => More (inr s)
      end.
  Proof.
    induction l; simpl; intros.
    - auto.
    - destruct b; auto.
  Qed.

  Definition lift2 {E S1 A S2 B C} (f : A -> B -> C) (a : t E S1 A) (b : t E S2 B) : t E _ C :=
    map (fun p => let '(a, b) := p in f a b) (pair a b).

  Lemma run_lift2_inl : forall E S1 A S2 B C (f : A -> B -> C) (a : t E S1 A) (b : t E S2 B) l s1 s2,
      run (lift2 f a b) (inl (s1, s2)) l =
      match run a s1 l with
      | Success (x, l) => run (lift2 f a b) (inr (x, s2)) l
      | More s1 => More (inl (s1, s2))
      end.
  Proof.
    intros.
    unfold lift2.
    rewrite run_map, run_pair_inl.
    destruct run; auto.
    destruct a0.
    rewrite run_map; auto.
  Qed.

  Lemma run_lift2_inr : forall E S1 A S2 B C (f : A -> B -> C) (a : t E S1 A) (b : t E S2 B) l x s,
      run (lift2 f a b) (inr (x, s)) l =
      match run b s l with
      | Success (y, l) => Success (f x y, l)
      | More s => More (inr (x, s))
      end.
  Proof.
    intros.
    unfold lift2.
    rewrite run_map, run_pair_inr.
    destruct run; auto.
    destruct a0; auto.
  Qed.

  Lemma run_lift2 : forall E S1 A S2 B C (f : A -> B -> C) (a : t E S1 A) (b : t E S2 B) l s1 s2,
      run (lift2 f a b) (inl (s1, s2)) l =
      match run a s1 l with
      | Success (x, l) =>
        match run b s2 l with
        | Success (y, l) => Success (f x y, l)
        | More s2 => More (inr (x, s2))
        end
      | More s1 => More (inl (s1, s2))
      end.
  Proof.
    intros.
    rewrite run_lift2_inl.
    destruct run; auto.
    destruct a0.
    rewrite run_lift2_inr. auto.
  Qed.

  Definition bind {E S1 A S2 B} (a : t E S1 A) (b : A -> t E S2 B) : t E _ B :=
    fun s e =>
      match s with
      | inl (s1, s2) =>
        match a s1 e with
        | Success x => More (inr (x, s2))
        | More s1 => More (inl (s1, s2))
        end
      | inr (x, s2) =>
        match b x s2 e with
        | Success y => Success y
        | More s2 => More (inr (x, s2))
        end
      end.

  Lemma run_bind_inl : forall E S1 A S2 B (a : t E S1 A) (b : A -> t E S2 B) l s1 s2,
      run (bind a b) (inl (s1, s2)) l =
      match run a s1 l with
      | Success (x, l) => run (bind a b) (inr (x, s2)) l
      | More s1 => More (inl (s1, s2))
      end.
  Proof.
    induction l; simpl; intros.
    - auto.
    - destruct a; auto.
  Qed.

  Lemma run_bind_inr : forall E S1 A S2 B (a : t E S1 A) (b : A -> t E S2 B) l x s2,
      run (bind a b) (inr (x, s2)) l =
      match run (b x) s2 l with
      | Success y => Success y
      | More s2 => More (inr (x, s2))
      end.
  Proof.
    induction l; simpl; intros.
    - auto.
    - destruct b; auto.
  Qed.

  Lemma run_bind : forall E S1 A S2 B (a : t E S1 A) (b : A -> t E S2 B) l s1 s2,
      run (bind a b) (inl (s1, s2)) l =
      match run a s1 l with
      | Success (x, l) =>
        match run (b x) s2 l with
        | Success y => Success y
        | More s2 => More (inr (x, s2))
        end
      | More s1 => More (inl (s1, s2))
      end.
  Proof.
    intros.
    rewrite run_bind_inl.
    destruct run; auto.
    destruct a0.
    now rewrite run_bind_inr.
  Qed.

  Definition repeat {E S A} (init : S) (a : t E S A) : t E _ (list A) :=
    fun s e =>
      let '(n, l, s) := s in
      match a s e with
      | Success x =>
        match n with
        | 0 => Success (rev_append l [x])
        | S n => More (n, x :: l, init)
        end
      | More s => More (n, l, s)
      end.

  Lemma run_repeat_once : forall E S A init (a : t E S A) bin l n s,
      run (repeat init a) (n, l, s) bin =
      match run a s bin with
      | Success (x, bin) =>
        match n with
        | 0 => Success (rev_append l [x], bin)
        | S n => run (repeat init a) (n, x :: l, init) bin
        end
      | More s => More (n, l, s)
      end.
  Proof.
    induction bin; simpl; intros.
    - auto.
    - destruct a; auto.
      destruct n; auto.
  Qed.

  Fixpoint denote_repeat {E S A} (n : nat) (acc : list A) (init : S) (a : t E S A) (bin : list E) :
    step_result _ _ :=
    match run a init bin with
    | Success (x, bin) =>
      match n with
      | 0 => Success (rev_append acc [x], bin)
      | S n => denote_repeat n (x :: acc) init a bin
      end
    | More s => More (n, acc, s)
    end.

  Lemma run_repeat : forall E S A init (a : t E S A) n bin acc,
      run (repeat init a) (n, acc, init) bin =
      denote_repeat n acc init a bin.
  Proof.
    induction n; simpl; intros; rewrite run_repeat_once.
    - auto.
    - destruct run; auto.
      destruct a0; auto.
  Qed.


  Definition bind' {E S1 A S2 B} (a : t E S1 A) (f : A -> step_result S2 B) (b : t E S2 B) :
    t E _ B :=
    fun s e =>
      match s with
      | inl s1 =>
        match a s1 e with
        | Success x =>
          match f x with
          | Success y => Success y
          | More s2 => More (inr s2)
          end
        | More s1 => More (inl s1)
        end
      | inr s2 =>
        match b s2 e with
        | Success y => Success y
        | More s2 => More (inr s2)
        end
      end.

  Lemma bind'_run_inl :
    forall E S1 A S2 B (a : t E S1 A) (f : A -> step_result S2 B) (b : t E S2 B) l s1,
      run (bind' a f b) (inl s1) l =
      match run a s1 l with
      | Success (x, l) =>
        match f x with
        | Success y => Success (y, l)
        | More s2 => run (bind' a f b) (inr s2) l
        end
      | More s => More (inl s)
      end.
  Proof.
    induction l; simpl; intros.
    - auto.
    - destruct a; auto.
      destruct f; auto.
  Qed.

  Lemma bind'_run_inr :
    forall E S1 A S2 B (a : t E S1 A) (f : A -> step_result S2 B) (b : t E S2 B) l s2,
      run (bind' a f b) (inr s2) l =
      match run b s2 l with
      | Success (y, l) => Success (y, l)
      | More s => More (inr s)
      end.
  Proof.
    induction l; simpl; intros.
    - auto.
    - destruct b; auto.
  Qed.

End automaton.

Module automata_deserializers.
  
  Definition bool_step : automaton.t bool unit bool := automaton.one.
  
  Definition option_step {S A} (init : S) (a : automaton.t bool S A) : automaton.t bool _ (option A) :=
    fun s b =>
      match s with
      | None => if b then More (Some init) else Success None
      | Some s =>
        match a s b with
        | Success x => Success (Some x)
        | More s => More (Some s)
        end
      end.
  
  Module positive.
    Inductive state :=
    | Start (k : positive -> positive)
    | OneMoreElt (k : positive -> positive).
  
    Definition step : automaton.t bool state positive :=
      fun s b =>
      match s with
      | Start k => if b then More (OneMoreElt k) else Success (k xH)
      | OneMoreElt k => More (Start (fun p => k ((if b then xI else xO) p)))
      end.
  
    Definition init := (Start (fun x => x)).
  
    Fixpoint serialize (p : positive) : list bool :=
      match p with
      | xI p => true :: true :: serialize p
      | xO p => true :: false :: serialize p
      | xH => [false]
      end.
  
    Lemma run_step :
      forall p bin k,
        automaton.run step (Start k) (serialize p ++ bin) =
        Success (k p, bin).
    Proof.
      induction p; simpl; intros.
      - now rewrite IHp.
      - now rewrite IHp.
      - auto.
    Qed.
  End positive.
  
  Definition N_step : automaton.t bool _ N :=
    fun s b =>
      match s with
      | None => if b then More (Some positive.init) else Success N0
      | Some s =>
        match positive.step s b with
        | Success p => Success (Npos p)
        | More s => More (Some s)
        end
      end.
  
  Definition N_init : option positive.state := None.
  
  Definition N_serialize (n : N) : list bool :=
    match n with
    | N0 => [false]
    | Npos p => true :: positive.serialize p
    end.
  
  Lemma run_N_step_Some :
    forall l s,
      automaton.run N_step (Some s) l =
      match automaton.run positive.step s l with
      | Success (p, l) => Success (Npos p, l)
      | More s => More (Some s)
      end.
  Proof.
    induction l; simpl; intros.
    - auto.
    - destruct positive.step; auto.
  Qed.
  
  Lemma run_N_step_init :
    forall n bin,
      automaton.run N_step N_init (N_serialize n ++ bin) =
      Success (n, bin).
  Proof.
    destruct n; simpl; intros.
    - auto.
    - rewrite run_N_step_Some.
      unfold positive.init.
      now rewrite positive.run_step.
  Qed.
  
  Definition nat_step : automaton.t bool _ nat := automaton.map N.to_nat N_step.
  
  Definition nat_init := N_init.
  
  Definition nat_serialize (n : nat) := N_serialize (N.of_nat n).
  
  Lemma run_nat_step :
    forall n bin,
      automaton.run nat_step nat_init (nat_serialize n ++ bin) =
      Success (n, bin).
  Proof.
    intros.
    unfold nat_serialize, nat_init, nat_step.
    now rewrite automaton.run_map, run_N_step_init, Nnat.Nat2N.id.
  Qed.
  
  Definition list_step {S A} (init : S) (a : automaton.t bool S A) : automaton.t bool _ (list A) :=
    automaton.bind' nat_step (fun n => match n with
                                    | 0 => Success []
                                    | S n => More (n, [], init)
                                    end)
                    (automaton.repeat init a).
  
  Definition list_init {A S} : option positive.state + nat * list A * S := inl (nat_init).
  
  Fixpoint list_serialize_rec {A} (a : A -> list bool) (l : list A) :=
    match l with
    | [] => []
    | x :: l => a x ++ list_serialize_rec a l
    end.
  
  Definition list_serialize {A} (a : A -> list bool) (l : list A) :=
    nat_serialize (length l) ++ list_serialize_rec a l.
  
  Lemma denote_repeat_list_serialize_rec :
    forall A S (a : automaton.t bool S A) (a_ser : A -> list bool) (init : S),
      (forall x bin, automaton.run a init (a_ser x ++ bin) = Success (x, bin)) ->
      forall n (l : list A)  acc bin,
      Datatypes.S n = length l ->
      automaton.denote_repeat n acc init a (list_serialize_rec a_ser l ++ bin) =
      Success (rev_append acc l, bin).
  Proof.
    induction n; destruct l; simpl; intros; try congruence.
    - rewrite app_assoc_reverse, H.
      destruct l; simpl in *; try congruence.
    - rewrite app_assoc_reverse, H.
      now rewrite IHn by congruence.
  Qed.
  
  Lemma run_list_step :
    forall S A (init : S) (a_ser : A -> list bool) (a : automaton.t bool S A) l bin,
      (forall x bin, automaton.run a init (a_ser x ++ bin) = Success (x, bin)) ->
      automaton.run (list_step init a) list_init (list_serialize a_ser l ++ bin) =
      Success (l, bin).
  Proof.
    intros.
    unfold list_step, list_init, list_serialize.
    rewrite app_assoc_reverse.
    rewrite automaton.bind'_run_inl.
    rewrite run_nat_step.
    destruct l; try solve [simpl; auto].
    cbn [length].
    rewrite automaton.bind'_run_inr, automaton.run_repeat.
    now rewrite denote_repeat_list_serialize_rec.
  Qed.
  
  
  Section list2.
  
    Definition list_step2 {S A} (init : S) (a : automaton.t bool S A) : automaton.t bool _ (list A) :=
      fun s b =>
        match s with
        | inl acc =>
          if b
          then More (inr (acc, init))
          else Success (rev_append acc [])
        | inr (acc, s) =>
          match a s b with
          | Success x => More (inl (x :: acc))
          | More s => More (inr (acc, s))
          end
        end.
  
    Fixpoint list_serialize2 {A} (a : A -> list bool) (l : list A) :=
      match l with
      | [] => [false]
      | x :: l => true :: a x ++ list_serialize2 a l
      end.
  
    Definition list_init2 {A S} : list A + list A * S := inl [].
  
    Lemma run_list_step2_inr :
      forall S A (init : S) (a : automaton.t bool S A) bin acc s,
      automaton.run (list_step2 init a) (inr (acc, s)) bin =
      match automaton.run a s bin with
      | Success (x, bin) =>
        automaton.run (list_step2 init a) (inl (x :: acc)) bin
      | More s => More (inr (acc, s))
      end.
    Proof.
      induction bin; simpl; intros.
      - auto.
      - destruct a; auto.
    Qed.
  
    Lemma run_list_step2' :
      forall S A (init : S) (a_ser : A -> list bool) (a : automaton.t bool S A) l bin acc,
      (forall x bin, automaton.run a init (a_ser x ++ bin) = Success (x, bin)) ->
      automaton.run (list_step2 init a) (inl acc) (list_serialize2 a_ser l ++ bin) =
      Success (rev_append acc l, bin).
    Proof.
      induction l; simpl; intros.
      - auto.
      - rewrite app_ass, run_list_step2_inr, H, IHl; auto.
    Qed.
  
    Lemma run_list_step2 :
      forall S A (init : S) (a_ser : A -> list bool) (a : automaton.t bool S A) l bin,
      (forall x bin, automaton.run a init (a_ser x ++ bin) = Success (x, bin)) ->
      automaton.run (list_step2 init a) list_init2 (list_serialize2 a_ser l ++ bin) =
      Success (l, bin).
    Proof.
      intros.
      apply run_list_step2'.
      auto.
    Qed.
  End list2.
  
  Module tree.
    Local Unset Elimination Schemes.
  
    Inductive t (A : Type) :=
    | atom (a : A)
    | node (l : list (t A)).
  
    Section rect.
      Variable A : Type.
      Variable P : t A -> Type.
      Variable Pl : list (t A) -> Type.
      Hypothesis Hatom : forall a, P (atom a).
      Hypothesis Hnode : forall l (IHl : Pl l), P (node l).
      Hypothesis Hnil : Pl [].
      Hypothesis Hcons : forall x l (IHx : P x) (IHl : Pl l), Pl (x :: l).
  
      Definition t_rect : forall (x : t A), P x :=
        fix go (x : t A) : P x :=
          let fix go_list (l : list (t A)) : Pl l :=
              match l with
              | [] => Hnil
              | x :: l => Hcons (go x) (go_list l)
              end
          in match x with
             | atom a => Hatom a
             | node l => Hnode (go_list l)
             end.
  
      Definition t_list_rect : forall l : list (t A), Pl l :=
        fix go_list (l : list (t A)) : Pl l :=
          match l with
          | [] => Hnil
          | x :: l => Hcons (t_rect x) (go_list l)
          end.
  
      Definition t_rect_and : (forall x, P x) * (forall l, Pl l) :=
        (t_rect, t_list_rect).
    End rect.
  
    Definition map A B (f : A -> B) : t A -> t B :=
      fix go t :=
        match t with
        | atom a => atom (f a)
        | node l => node (List.map go l)
        end.
  
    Definition stack A := list (list (t A)).
  
    Inductive state (S A : Type) : Type :=
    | Start : state S A
    | Atom : S -> state S A
    | Node : list (t A) -> state S A.
    Arguments Start {_} {_}.
    Arguments Atom {_} {_} _.
    Arguments Node {_} {_} _.
  
    Definition pop {S A} (ans : t A) (stk : stack A) : step_result (state S A * stack A) (t A)  :=
      match stk with
      | [] => Success ans
      | l :: stk => More (Node (ans :: l), stk)
      end.
  
    Definition step {S A} (init : S) (a : automaton.t bool S A) : automaton.t bool _ (t A) :=
      fun s b =>
      match s with
      | (Start, stk) =>
        if b
        then More (Node [], stk)
        else More (Atom init, stk)
      | (Node acc, stk) =>
        if b
        then More (Start, acc :: stk)
        else pop (node (rev_append acc [])) stk
      | (Atom s, stk) =>
        match a s b with
        | More s => More (Atom s, stk)
        | Success x => pop (atom x) stk
        end
      end.
  
    Definition serialize_tree {A} (a_ser : A -> list bool) : t A -> list bool :=
      fix go (t0 : t A) : list bool :=
        let fix go_list (l : list (t A)) : list bool :=
            match l with
            | [] => [false]
            | t0 :: l => true :: go t0 ++ go_list l
            end
        in match t0 with
           | atom a => false :: a_ser a
           | node l => true :: go_list l
           end.
  
    Definition serialize_tree_list {A} (a_ser : A -> list bool) : list (t A) -> list bool :=
      fix go_list (l : list (t A)) : list bool :=
        match l with
        | [] => [false]
        | t0 :: l => true :: serialize_tree a_ser t0 ++ go_list l
        end.
  
    Lemma run_step_Atom :
      forall S A init (a : automaton.t bool S A) bin s stk,
        automaton.run (step init a) (Atom s, stk) bin =
        match automaton.run a s bin with
        | Success (x, bin) =>
          match pop (atom x) stk with
          | Success t0 => Success (t0, bin)
          | More y =>
            automaton.run (step init a) y bin
          end
        | More s => More (Atom s, stk)
        end.
    Proof.
      induction bin; simpl; intros.
      - auto.
      - destruct a; auto.
    Qed.
  
    Lemma run_step' :
      forall S A init (a : automaton.t bool S A) a_ser,
        (forall x bin, automaton.run a init (a_ser x ++ bin) = Success (x, bin)) ->
        (forall t0 stk bin,
            automaton.run (step init a) (Start, stk) (serialize_tree a_ser t0 ++ bin) =
            match pop t0 stk with
            | Success t0 => Success (t0, bin)
            | More y => automaton.run (step init a) y bin
            end) *
        (forall l acc stk bin,
            automaton.run (step init a) (Node acc, stk) (serialize_tree_list a_ser l ++ bin) =
            match pop (node (rev_append acc l)) stk with
            | Success t0 => Success (t0, bin)
            | More y => automaton.run (step init a) y bin
            end).
    Proof.
      intros S A init a a_ser Ha_ser.
      apply t_rect_and; simpl; intros.
      - rewrite run_step_Atom, Ha_ser. auto.
      - rewrite IHl. auto.
      - auto.
      - rewrite app_ass, IHx.
        simpl. rewrite IHl. auto.
    Qed.
  End tree.
End automata_deserializers.
