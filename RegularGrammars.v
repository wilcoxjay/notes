(* Playing around in response to

   https://sympa.inria.fr/sympa/arc/coq-club/2017-05/msg00062.html

*)

Require Import List.
Import ListNotations.
Require Import Classes.EquivDec.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

(* First, some library helper functions and notations. *)

Instance option_eqdec A `(EqDec A eq) : EqDec (option A) eq :=
{
  equiv_dec x y :=
    match x, y with
      | Some a, Some b => if a == b then left _ else right _
      | None, None => left _
      | Some _, None | None, Some _ => right _
    end
 }.
all: congruence.
Defined.


Definition filterMap {A B} (f : A -> option B) : list A -> list B :=
  fix rec (l : list A) : list B :=
    match l with
    | [] => []
    | x :: l => match f x with
               | None => rec l
               | Some y => y :: rec l
               end
    end.

Fixpoint list_option_traverse {A} (l : list (option A)) : option (list A) :=
  match l with
  | [] => Some []
  | x :: l =>
    match x with
    | None => None
    | Some a =>
      match list_option_traverse l with
      | None => None
      | Some l => Some (a :: l)
      end
    end
  end.

Notation "x |> f" := (f x) (left associativity, at level 69, only parsing) .


(* A type representing valid right-hand sides of left-regular grammar rules.
   The original email used a much looser representation of rules, which did not
   separate the LHS from the RHS, and which did not enforce regularity. By
   restricting the representation, we make it easier to write a parser. *)
Module rhs.
  Inductive t T NT :=
  | Empty : t T NT
  | Single : T -> t T NT
  | Continue : T -> NT -> t T NT
  .

  Arguments Empty {_} {_}.
  Arguments Single {_} {_} _.

  Definition isEmpty T NT (rhs : rhs.t T NT) : bool :=
    match rhs with
    | Empty => true
    | _ => false
    end.

  Module exports.
    Notation Empty := Empty.
    Notation Single := Single.
    Notation Continue := Continue.
  End exports.
End rhs.
Import rhs.exports.

Module reg_grammar.
  Section reg_grammar.
    Variable T NT : Type.
    Context `{EqDec T eq} `{EqDec NT eq}.

  Record t : Type:= {
      start_symbol: NT;
      rules : list(NT * rhs.t T NT)
  }.

  (* Next, we're going to write a function [parse] that decides whether a string
     is in the language represented by the grammar. The parser keeps track of
     the set of nonterminal symbols it's currently in, with the additonal
     special symbol None representing "end of string when the last rule applied
     had RHS [Single]". *)

  (* It may help to scroll down to the function [parse] first, and read
     backwards up to here. *)

  (* Given the RHS of a rule and a terminal, decides whether the RHS can be used. *)
  Definition step_rhs (t : T) (rhs : rhs.t T NT) : list (option NT) :=
    match rhs with
    | Empty => []
    | Single t' => if t == t' then [None] else []
    | Continue t' nt => if t == t' then [Some nt] else []
    end.
  
  (* Finds all the productions for a given nonterminal. *)
  Definition getRHS T NT `{EqDec NT eq}
           (nt : NT) : list (NT * rhs.t T NT) ->
                       list (rhs.t T NT) :=
    filterMap (fun rule => let '(nt', rhs) := rule in
                        if nt == nt' then Some rhs else None).
  
  (* Given a nonterminal [nt], applies all possible rules. *)
  Definition step_nt (rules : list(NT * rhs.t T NT)) (t : T) (nt : NT) : list (option NT) :=
    rules |> getRHS nt
          |> flat_map (step_rhs t).
  
  (* Given a *list* of nonterminals, takes all possible next steps. *)
  Definition step (rules : list(NT * rhs.t T NT)) (t : T) (acc : list NT) : list (option NT) :=
    acc |> flat_map (step_nt rules t)
        |> nodup equiv_dec.
  
  (* The main parser loop. Repeatedly steps the current set of states using
     terminals from the string. *)
  Definition parse' (rules : list(NT * rhs.t T NT))
           : list T -> list (option NT) -> list (option NT) :=
    fix rec l acc :=
      match l with
      | [] => acc
      | t :: l =>
        acc |> filterMap id
            |> step rules t
            |> rec l
      end.

  Lemma parse'_nil :
    forall g l ,
      reg_grammar.parse' g l [] = [].
  Proof.
    induction l; simpl; auto.
  Qed.

  Lemma parse'_app :
    forall g l1 l2 acc,
      acc |> parse' g (l1 ++ l2) =
      acc |> parse' g l1 |> parse' g l2.
  Proof.
    induction l1; simpl; auto.
  Qed.

  (* Checks to see if the current state represents an accepting state.  In this
     representataion of state, a state is accepting if it contains [None] or if
     it contains [Some nt] and there is a rule [(nt, Empty)].  *)
  Definition is_final (rules : list (NT * rhs.t T NT)) (l : list (option NT)) : bool :=
    existsb (fun o => match o with
                   | None => true
                   | Some nt => getRHS nt rules |> existsb rhs.isEmpty
                   end)
            l.

  (* Top-level parse function. Calls [parse'] with the initial symbol and checks
     to see whether the resulting state is accepting. *)
  Definition parse (grammar : reg_grammar.t) (l : list T):=
    [Some (start_symbol grammar)]
        |> parse' (rules grammar) l
        |> is_final (rules grammar).

  Definition rhs_from_loose (l : list (NT + T)) : option (rhs.t T NT) :=
    match l with
    | [] => Some Empty
    | [inr t] => Some (Single t)
    | [inr t; inl A] => Some (Continue t A)
    | _ => None
    end.

  Definition rule_from_loose (l : list (NT + T)) : option (NT * rhs.t T NT) :=
    match l with
    | inl A :: rhs =>
      match rhs_from_loose rhs with
      | None => None
      | Some rhs => Some (A, rhs)
      end
    | _ => None
    end.

  Definition rules_from_loose (l : list (list (NT + T))) : option (list (NT * rhs.t T NT)) :=
    l |> map rule_from_loose
      |> list_option_traverse.

  Definition from_loose (start : NT) (l : list (list (NT + T))) : option t :=
    match rules_from_loose l with
    | None => None
    | Some rs => Some {| start_symbol := start;
                        rules := rs |}
    end.
  End reg_grammar.
End reg_grammar.

Module dfa.
  Section dfa.
    Variable (S A : Type).
    Record t := DFA {
      initial_state : S;
      is_final : S -> bool;
      next : S -> A -> S
   }.

    Definition run' (step: S -> A -> S) (l : list A) (acc : S) : S :=
      fold_left step l acc.

    Lemma run'_app : forall f l1 l2 acc,
        acc |> run' f (l1 ++ l2) =
        acc |> run' f l1 |> run' f l2.
    Proof.
      induction l1; simpl; auto.
    Qed.

    Definition run (m : t) (l : list A) : bool :=
      is_final m (run' (next m) l (initial_state m)).
  End dfa.
End dfa.

(* We can explicitly construct a DFA corresponding to the grammar. In fact, all
   the hard work was already done in our grammar parser. *)
Module powerset_construction.
  Section powerset_construction.
    Variable T NT : Type.
    Context `{EqDec T eq} `{EqDec NT eq}.

    Variable g : reg_grammar.t T NT.

    Definition state : Type := list (option NT).

    Definition init : state := [Some (reg_grammar.start_symbol g)].

    Definition is_final (s : state) : bool :=
      reg_grammar.is_final (reg_grammar.rules g) s.

    Definition next (s : state) (t : T) : state :=
      reg_grammar.step (reg_grammar.rules g) t (filterMap id s).

    Definition dfa := dfa.DFA init is_final next.

    (* Because of the way we carefully set this up, simulation holds
       *definitionally*, which is pretty cool. *)
    Theorem simulation : forall l, dfa.run dfa l = reg_grammar.parse g l.
    Proof.
      reflexivity.
    Qed.
  End powerset_construction.
End powerset_construction.

(* A simple example language over the alphabet {a,b} corresponding to the
   regular expression

       a*b*

   (Note that the original email contained an incorrect grammar for this
   language. A correct one is given below.) *)
Module a_b_example.
  Module non_terminal.
    Inductive t:Type :=
      A | B.

    Instance eqdec : EqDec t eq :=
      { equiv_dec x y :=
          match x, y with
          | A, A => left _
          | B, B => left _
          | A, B | B, A => right _
          end
      }.
    all: congruence.
    Defined.
  End non_terminal.

  Module terminal.
    Inductive t : Type :=
      a | b.

    Instance eqdec : EqDec t eq :=
      { equiv_dec x y :=
          match x, y with
          | a, a => left _
          | b, b => left _
          | a, b | b, a => right _
          end
      }.
    all: congruence.
    Defined.
  End terminal.

  Definition a_b_rules: list(non_terminal.t * rhs.t terminal.t non_terminal.t):=
    [(non_terminal.A, Continue terminal.a non_terminal.A);
     (non_terminal.A, Continue terminal.b non_terminal.B);
     (non_terminal.A, Empty);
     (non_terminal.B, Continue terminal.b non_terminal.B);
     (non_terminal.B, Empty)].

  Definition a_b_grammar : reg_grammar.t terminal.t non_terminal.t :=
    {| reg_grammar.start_symbol := non_terminal.A;
       reg_grammar.rules := a_b_rules |}.

  (* A few examples. *)
  Eval compute in reg_grammar.parse a_b_grammar [].
  Eval compute in reg_grammar.parse a_b_grammar [terminal.a].
  Eval compute in reg_grammar.parse a_b_grammar [terminal.a; terminal.a].
  Eval compute in reg_grammar.parse a_b_grammar [terminal.b; terminal.b].
  Eval compute in reg_grammar.parse a_b_grammar [terminal.a; terminal.b].
  Eval compute in reg_grammar.parse a_b_grammar [terminal.b; terminal.a].


  Definition a_b_spec (l : list terminal.t) : Prop :=
    exists n1 n2,
      l = repeat terminal.a n1 ++ repeat terminal.b n2.

  Lemma a_b_grammar_step_B :
    forall a,
      a = terminal.a /\ reg_grammar.step a_b_rules a [non_terminal.B] = [] \/
      a = terminal.b /\ reg_grammar.step a_b_rules a [non_terminal.B] = [Some non_terminal.B].
  Proof.
    destruct a; intuition.
  Qed.

  Lemma a_b_grammar_step_A :
    forall a,
      a = terminal.a /\ reg_grammar.step a_b_rules a [non_terminal.A] = [Some non_terminal.A] \/
      a = terminal.b /\ reg_grammar.step a_b_rules a [non_terminal.A] = [Some non_terminal.B].
  Proof.
    destruct a; intuition.
  Qed.

  Lemma a_b_grammar_parse'_B :
    forall l ,
      reg_grammar.parse' a_b_rules l [Some non_terminal.B] = [Some non_terminal.B] \/
      reg_grammar.parse' a_b_rules l [Some non_terminal.B] = [].
  Proof.
    induction l; simpl.
    - intuition.
    - destruct (a_b_grammar_step_B a) as [[Ha Hstep]|[Ha Hstep]]; subst a; rewrite Hstep.
      + rewrite reg_grammar.parse'_nil. auto.
      + auto.
  Qed.

  Lemma a_b_grammar_parse'_A :
    forall l ,
      reg_grammar.parse' a_b_rules l [Some non_terminal.A] = [Some non_terminal.A] \/
      reg_grammar.parse' a_b_rules l [Some non_terminal.A] = [Some non_terminal.B] \/
      reg_grammar.parse' a_b_rules l [Some non_terminal.A] = [].
  Proof.
    induction l; simpl.
    - intuition.
    - destruct (a_b_grammar_step_A a) as [[Ha Hstep]|[Ha Hstep]]; subst a; rewrite Hstep.
      + auto.
      + destruct (a_b_grammar_parse'_B l) as [H|H]; rewrite H; auto.
  Qed.

  Lemma a_b_grammar_parse'_BB_sound :
    forall l ,
      reg_grammar.parse' a_b_rules l [Some non_terminal.B] = [Some non_terminal.B] ->
      exists n, l = repeat terminal.b n.
  Proof.
    induction l; simpl; intros.
    - exists 0. auto.
    - destruct (a_b_grammar_step_B a) as [[? Hstep]|[? Hstep]]; subst a;
        rewrite Hstep in *.
      + rewrite reg_grammar.parse'_nil in H. discriminate.
      + apply IHl in H.
        destruct H as [n H].
        exists (S n).
        simpl. congruence.
  Qed.

  Lemma a_b_grammar_parse'_AA_sound :
    forall l ,
      reg_grammar.parse' a_b_rules l [Some non_terminal.A] = [Some non_terminal.A] ->
      exists n, l = repeat terminal.a n.
  Proof.
    induction l; simpl; intros.
    - exists 0. auto.
    - destruct (a_b_grammar_step_A a) as [[? Hstep]|[? Hstep]]; subst a;
        rewrite Hstep in *.
      + apply IHl in H.
        destruct H as [n H].
        exists (S n).
        simpl. congruence.
      + destruct (a_b_grammar_parse'_B l) as [Hp|Hp]; rewrite Hp in H; discriminate.
  Qed.

  Lemma a_b_grammar_parse'_AB_sound :
    forall l ,
      reg_grammar.parse' a_b_rules l [Some non_terminal.A] = [Some non_terminal.B] ->
      a_b_spec l.
  Proof.
    induction l; simpl; intros.
    - exists 0, 0. auto.
    - destruct (a_b_grammar_step_A a) as [[? Hstep]|[? Hstep]]; subst a;
        rewrite Hstep in *.
      + apply IHl in H.
        destruct H as (n1 & n2 & H).
        exists (S n1), n2.
        simpl. congruence.
      + apply a_b_grammar_parse'_BB_sound in H.
        destruct H as [n H].
        exists 0, (S n). simpl. congruence.
  Qed.

  Lemma a_b_grammar_sound :
    forall l,
      reg_grammar.parse a_b_grammar l = true ->
      a_b_spec l.
  Proof.
    unfold reg_grammar.parse.
    cbn.
    intros l.
    destruct (a_b_grammar_parse'_A l) as [H|[H|H]]; rewrite H; intros E.
    - apply a_b_grammar_parse'_AA_sound in H.
      destruct H as [n H].
      exists n, 0.
      simpl. rewrite app_nil_r. auto.
    - auto using a_b_grammar_parse'_AB_sound.
    - discriminate.
  Qed.

  Lemma a_b_grammar_parse'_AA_complete :
    forall n,
      reg_grammar.parse' a_b_rules (repeat terminal.a n) [Some non_terminal.A] =
      [Some non_terminal.A].
  Proof.
    induction n; simpl; auto.
  Qed.

  Lemma a_b_grammar_parse'_BB_complete :
    forall n,
      reg_grammar.parse' a_b_rules (repeat terminal.b n) [Some non_terminal.B] =
      [Some non_terminal.B].
  Proof.
    induction n; simpl; auto.
  Qed.

  Lemma a_b_grammar_parse'_AB_complete :
    forall n,
      reg_grammar.parse' a_b_rules (repeat terminal.b n) [Some non_terminal.A] =
      match n with
      | 0 => [Some non_terminal.A]
      | S _ => [Some non_terminal.B]
      end.
  Proof.
    destruct n; simpl; auto using a_b_grammar_parse'_BB_complete.
  Qed.

  Lemma a_b_grammar_complete :
    forall l,
      a_b_spec l ->
      reg_grammar.parse a_b_grammar l = true.
  Proof.
    unfold reg_grammar.parse.
    cbn.
    intros l (n1 & n2 & H). subst l.
    rewrite reg_grammar.parse'_app, a_b_grammar_parse'_AA_complete,
            a_b_grammar_parse'_AB_complete.
    destruct n2; reflexivity.
  Qed.

  (* A hand rolled DFA for the same language. *)
  Definition a_b_next (s : option non_terminal.t) (t : terminal.t) : option non_terminal.t :=
    match s with
    | None => None
    | Some non_terminal.A =>
      match t with
      | terminal.a => Some non_terminal.A
      | terminal.b => Some non_terminal.B
      end
    | Some non_terminal.B =>
      match t with
      | terminal.a => None
      | terminal.b => Some non_terminal.B
      end
    end.

  Definition a_b_is_final (s : option non_terminal.t) : bool :=
    match s with
    | None => false
    | Some _ => true
    end.

  Definition a_b_dfa : dfa.t _ _ :=
    {| dfa.initial_state := Some non_terminal.A;
       dfa.is_final := a_b_is_final;
       dfa.next := a_b_next
    |}.

  Lemma a_b_dfa_run'_None :
    forall l,
      dfa.run' a_b_next l None = None.
  Proof.
    induction l; simpl; auto.
  Qed.


  Lemma a_b_dfa_run'_B :
    forall l s',
      dfa.run' a_b_next l (Some non_terminal.B) = Some s' ->
      exists n, l = List.repeat terminal.b n.
  Proof.
    induction l; simpl; intros.
    - exists 0. auto.
    - destruct a.
      + rewrite a_b_dfa_run'_None in *. discriminate.
      + apply IHl in H. destruct H as [n H]. subst. exists (S n). auto.
  Qed.


  Lemma a_b_dfa_run'_A :
    forall l s',
      dfa.run' a_b_next l (Some non_terminal.A) = Some s' ->
      a_b_spec l.
  Proof.
    induction l; simpl; intros.
    - exists 0, 0. auto.
    - destruct a.
      + apply IHl in H. destruct H as (n1 & n2 & H). subst. exists (S n1), n2. auto.
      + apply a_b_dfa_run'_B in H. destruct H as [n H]. subst. exists 0, (S n). auto.
  Qed.

  Lemma a_b_dfa_sound :
    forall l,
      dfa.run a_b_dfa l = true ->
      a_b_spec l.
  Proof.
    unfold dfa.run.
    cbn.
    intros.
    destruct (dfa.run' _ _ _) eqn:?; try discriminate.
    eauto using a_b_dfa_run'_A.
  Qed.

  Lemma a_b_dfa_run'_AA_complete :
    forall n,
      dfa.run' a_b_next (repeat terminal.a n) (Some non_terminal.A) = Some non_terminal.A.
  Proof.
    induction n; simpl; auto.
  Qed.

  Lemma a_b_dfa_run'_BB_complete :
    forall n,
      dfa.run' a_b_next (repeat terminal.b n) (Some non_terminal.B) = Some non_terminal.B.
  Proof.
    induction n; simpl; auto.
  Qed.

  Lemma a_b_dfa_run'_AB_complete :
    forall n,
      dfa.run' a_b_next (repeat terminal.b n) (Some non_terminal.A) =
      match n with
      | 0 => Some non_terminal.A
      | S _ => Some non_terminal.B
      end.
  Proof.
    destruct n; simpl; auto using a_b_dfa_run'_BB_complete.
  Qed.

  Lemma a_b_dfa_complete :
    forall l,
      a_b_spec l ->
      dfa.run a_b_dfa l = true.
  Proof.
    unfold dfa.run, a_b_spec.
    cbn.
    intros l (n1 & n2 & ?). subst.
    rewrite dfa.run'_app.
    rewrite a_b_dfa_run'_AA_complete.
    rewrite a_b_dfa_run'_AB_complete.
    destruct n2; auto.
  Qed.

  (* Examples running the DFA. *)
  Eval compute in dfa.run a_b_dfa [].
  Eval compute in dfa.run a_b_dfa [terminal.a].
  Eval compute in dfa.run a_b_dfa [terminal.a; terminal.a].
  Eval compute in dfa.run a_b_dfa [terminal.b; terminal.b].
  Eval compute in dfa.run a_b_dfa [terminal.a; terminal.b].
  Eval compute in dfa.run a_b_dfa [terminal.b; terminal.a].

  (* Automatically construct a DFA using the powerset construction. *)
  Definition a_b_dfa' := powerset_construction.dfa a_b_grammar.

  (* Examples running the second DFA. *)
  Eval compute in dfa.run a_b_dfa' [].
  Eval compute in dfa.run a_b_dfa' [terminal.a].
  Eval compute in dfa.run a_b_dfa' [terminal.a; terminal.a].
  Eval compute in dfa.run a_b_dfa' [terminal.b; terminal.b].
  Eval compute in dfa.run a_b_dfa' [terminal.a; terminal.b].
  Eval compute in dfa.run a_b_dfa' [terminal.b; terminal.a].


  (* The same (corrected) grammar, represented in the loose format used in the
     original email. *)
  Definition a_b_loose_rules: list(list(non_terminal.t + terminal.t)) :=
    [[inl non_terminal.A; inr terminal.a; inl non_terminal.A];
     [inl non_terminal.A; inr terminal.b; inl non_terminal.B];
     [inl non_terminal.A];
     [inl non_terminal.B; inr terminal.b; inl non_terminal.B];
     [inl non_terminal.B]].

  (* We can see that it gets converted to the "tight" representation given
     above. *)
  Eval compute in reg_grammar.from_loose non_terminal.A a_b_loose_rules.

  Ltac grab_option x :=
    let x' := eval compute in x in
    match x' with
    | Some ?v => exact v
    end.

  Definition a_b_from_loose :=
    ltac:(grab_option (reg_grammar.from_loose non_terminal.A a_b_loose_rules)).
End a_b_example.
