(* Playing around in response to

   https://sympa.inria.fr/sympa/arc/coq-club/2017-05/msg00062.html

*)

Require Import List.
Import ListNotations.
Require Import Classes.EquivDec.
Require Import Coq.Program.Program.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Obligation Tactic := unfold complement, equiv ; program_simpl.
Program Instance option_eqdec A `(EqDec A eq) : EqDec (option A) eq :=
{
  equiv_dec x y :=
    match x, y with
      | Some a, Some b => if a == b then in_left else in_right
      | None, None => in_left
      | Some _, None | None, Some _ => in_right
    end
 }.


Definition filterMap {A B} (f : A -> option B) : list A -> list B :=
  fix rec (l : list A) : list B :=
    match l with
    | [] => []
    | x :: l => match f x with
               | None => rec l
               | Some y => y :: rec l
               end
    end.

Notation "x |> f" := (f x) (left associativity, at level 98, only parsing) .

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

  (* We track a set of nonterminal symbols we're currently in,
     with the additonal special symbol None representing "end of string". *)
  Definition step_rhs (t : T) (rhs : rhs.t T NT) : list (option NT) :=
    match rhs with
    | Empty => []
    | Single t' => if t == t' then [None] else []
    | Continue t' nt => if t == t' then [Some nt] else []
    end.
  
  
  Definition getRHS T NT `{EqDec NT eq}
           (nt : NT) : list (NT * rhs.t T NT) ->
                       list (rhs.t T NT) :=
    filterMap (fun rule => let '(nt', rhs) := rule in
                        if nt == nt' then Some rhs else None).
  
  Definition step_nt (rules : list(NT * rhs.t T NT)) (t : T) (nt : NT) : list (option NT) :=
    rules |> getRHS nt
          |> flat_map (step_rhs t).
  
  Definition step (rules : list(NT * rhs.t T NT)) (t : T) (acc : list NT) : list (option NT) :=
    acc |> flat_map (step_nt rules t)
        |> nodup equiv_dec.
  
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

  Definition parse (grammar : reg_grammar.t) (l : list T):=
    [Some (start_symbol grammar)]
        |> parse' (rules grammar) l
        |> existsb (fun o => match o with
                          | None => true
                          | Some nt => getRHS nt (rules grammar) |> existsb rhs.isEmpty
                          end).
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

    Definition run (m : t) (l : list A) : bool :=
      is_final m (run' (next m) l (initial_state m)).

  End dfa.
End dfa.

Module a_b_example.
  Module non_terminal.
    Inductive t:Type :=
      A | B.

    Program Instance eqdec : EqDec t eq :=
      { equiv_dec x y :=
          match x, y with
          | A, A => in_left
          | B, B => in_left
          | A, B | B, A => in_right
          end
      }.
  End non_terminal.

  Module terminal.
    Inductive t : Type :=
      a | b.

    Program Instance eqdec : EqDec t eq :=
      { equiv_dec x y :=
          match x, y with
          | a, a => in_left
          | b, b => in_left
          | a, b | b, a => in_right
          end
      }.
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

  Eval compute in reg_grammar.parse a_b_grammar [].
  Eval compute in reg_grammar.parse a_b_grammar [terminal.a].
  Eval compute in reg_grammar.parse a_b_grammar [terminal.a; terminal.a].
  Eval compute in reg_grammar.parse a_b_grammar [terminal.b; terminal.b].
  Eval compute in reg_grammar.parse a_b_grammar [terminal.a; terminal.b].
  Eval compute in reg_grammar.parse a_b_grammar [terminal.b; terminal.a].


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

  Eval compute in dfa.run a_b_dfa [].
  Eval compute in dfa.run a_b_dfa [terminal.a].
  Eval compute in dfa.run a_b_dfa [terminal.a; terminal.a].
  Eval compute in dfa.run a_b_dfa [terminal.b; terminal.b].
  Eval compute in dfa.run a_b_dfa [terminal.a; terminal.b].
  Eval compute in dfa.run a_b_dfa [terminal.b; terminal.a].
End a_b_example.
