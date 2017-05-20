Require Import List Omega.
Import ListNotations.

Set Implicit Arguments.

Ltac break X :=
  match X with
  | context [match ?X with _ => _ end] => break X
  | _ => destruct X eqn:?
  end.

Ltac break_match :=
  match goal with
  | [ |- context [match ?X with _ => _ end] ] => break X
  | [ H : context [match ?X with _ => _ end] |- _ ] => break X
  end.

Ltac inv H := inversion H; subst.
Ltac invc H := inversion H; subst; clear H.

Module error.
Inductive t (E A : Type) : Type :=
| Ok : A -> t E A
| Err : E -> t E A.
Arguments Ok {_} {_} _.
Arguments Err {_} {_} _.
Module exports.
Notation Ok := Ok.
Notation Err := Err.
End exports.
End error.
Import error.exports.

(* Unlike the early-exit automata in other files. Classical parsing
   expects to consume the whole string. *)
Module automaton.
  Record t (M E S A : Type) : Type := Make {
    step : S -> E -> error.t M S;
    finish : S -> error.t M A
  }.

  Definition run' {M E S A} (a : t M E S A) : list E -> S -> error.t M S :=
    fix go (l : list E) (s : S) : error.t M S :=
      match l with
      | [] => Ok s
      | e :: l =>
        match step a s e with
        | Ok s => go l s
        | Err msg => Err msg
        end
      end.

  Lemma run'_app :
    forall M E S A (a : automaton.t M E S A) es es' s ,
      automaton.run' a (es ++ es') s =
      match automaton.run' a es s with
      | Err msg => Err msg
      | Ok s' => automaton.run' a es' s'
      end.
  Proof.
    induction es; simpl; intros; try break_match; auto.
  Qed.

  Definition run {M E S A} (a : t M E S A) (l : list E) (init : S) : error.t M A :=
    match run' a l init with
    | Err msg => Err msg
    | Ok s => finish a s
    end.
End automaton.

(* The rest of the file is an extended example parsing arithmetic
   expressions. *)

Module exp.
Inductive t :=
| Const : nat -> t
| Plus : t -> t -> t.
End exp.

Module token.
Inductive t :=
| LParen
| RParen
| Plus
| Const : nat -> t.
End token.

Module grammar.
(*
original grammar (ambiguous):

e ::= n
    | '(' e ')'
    | e '+' e

---------------------
apply left associativity to '+':

e ::= a
    | e '+' a

a ::= n
    | '(' e ')'

---------------------
avoiding left recursion but using kleene star:

e ::= a ('+' a)*

a ::= n
    | '(' e ')'

*)

(* Encoding the second grammar above. *)
Local Unset Elimination Schemes.
Inductive atom : exp.t -> list token.t -> Prop :=
| Const : forall n, atom (exp.Const n) [token.Const n]
| Paren : forall e ts, exp e ts -> atom e (token.LParen :: ts ++ [token.RParen])
with exp : exp.t -> list token.t -> Prop :=
| Plus : forall e ts1 a ts2, exp e ts1 -> atom a ts2 -> exp (exp.Plus e a) (ts1 ++ token.Plus :: ts2)
| Atom : forall e ts, atom e ts -> exp e ts
.
Hint Constructors atom exp.

Scheme atom_ind := Induction for atom Sort Prop
with exp_ind := Induction for exp Sort Prop.
Combined Scheme exp_atom_ind from atom_ind, exp_ind.
End grammar.

Module side.
Inductive t := left | right.
End side.

Definition needs_parens (s : side.t) (e : exp.t) : bool :=
  match e with
  | exp.Const _ => false
  | exp.Plus _ _ =>
    match s with
    | side.left => false
    | side.right => true
    end
  end.

Fixpoint unparse (side : side.t) (e : exp.t) : list token.t :=
  let ans :=
      match e with
      | exp.Const n => [token.Const n]
      | exp.Plus e1 e2 => unparse side.left e1 ++ token.Plus :: unparse side.right e2
      end
  in if needs_parens side e
     then token.LParen :: ans ++ [token.RParen]
     else ans.

Lemma unparse_correct' :
  forall e, grammar.exp e (unparse side.left e) /\
       grammar.atom e (unparse side.right e).
Proof.
  induction e; split; simpl; intuition eauto.
Qed.

Lemma unparse_correct :
  forall e, grammar.exp e (unparse side.left e).
Proof.
  apply unparse_correct'.
Qed.

Definition e12 := (exp.Plus (exp.Const 1) (exp.Const 2)).
Definition e123l := (exp.Plus (exp.Plus (exp.Const 1) (exp.Const 2)) (exp.Const 3)).
Definition e123r := (exp.Plus (exp.Const 1) (exp.Plus (exp.Const 2) (exp.Const 3))).

Eval compute in unparse side.left e12.
Eval compute in unparse side.left e123l.
Eval compute in unparse side.left e123r.


Module top_down.
Inductive exp : list token.t -> exp.t -> Prop :=
| Atom : forall ts1 ts2 a l,
    atom ts1 a ->
    atom_plus_list ts2 l ->
    exp (ts1 ++ ts2) (fold_left exp.Plus l a)
with atom : list token.t -> exp.t -> Prop :=
| Const : forall n, atom [token.Const n] (exp.Const n)
| Paren : forall ts e,
  exp ts e ->
  atom (token.LParen :: ts ++ [token.RParen]) e
with atom_plus_list : list token.t -> list exp.t -> Prop :=
| Nil : atom_plus_list [] []
| Cons : forall ts1 ts2 a l,
    atom ts1 a ->
    atom_plus_list ts2 l ->
    atom_plus_list (token.Plus :: ts1 ++ ts2) (a :: l)
.
Hint Constructors exp atom atom_plus_list.

Scheme exp_ind' := Induction for exp Sort Prop
with atom_ind' := Induction for atom Sort Prop
with atom_plus_list_ind' := Induction for atom_plus_list Sort Prop.
Combined Scheme exp_atom_atom_plus_list_ind from exp_ind', atom_ind', atom_plus_list_ind'.

Lemma to_grammar :
  (forall ts e, exp ts e -> grammar.exp e ts) /\
  (forall ts a, atom ts a -> grammar.atom a ts) /\
  (forall ts l, atom_plus_list ts l -> forall x ts', grammar.exp x ts' ->
                                          grammar.exp (fold_left exp.Plus l x) (ts' ++ ts)).
Proof.
  apply exp_atom_atom_plus_list_ind; intros; auto.
  - simpl. rewrite app_nil_r. auto.
  - simpl. rewrite app_comm_cons, app_assoc. auto.
Qed.

Lemma fold_left_outer :
  forall A B (f : A -> B -> A) l a b,
    f (fold_left f l a) b = fold_left f (l ++ [b]) a.
Proof.
  induction l; simpl; auto.
Qed.

Lemma atom_plus_list_snoc :
  forall ts1 ts2 a l,
    atom ts1 a ->
    atom_plus_list ts2 l ->
    atom_plus_list (ts2 ++ token.Plus :: ts1) (l ++ [a]).
Proof.
  intros.
  revert a ts1 H.
  induction H0; intros.
  - simpl. eapply Cons with (ts2 := []) (l := []) in H; auto.
    rewrite app_nil_r in *. auto.
  - simpl. rewrite app_ass. auto.
Qed.

Lemma exp_of_atom :
  forall a ts,
    atom ts a ->
    exp ts a.
Proof.
  intros.
  eapply Atom with (ts2 := [])(l := []) in H; auto.
  rewrite app_nil_r in *. simpl in *. auto.
Qed.

Lemma from_grammar :
  (forall a ts, grammar.atom a ts -> atom ts a) /\
  (forall e ts, grammar.exp e ts -> exp ts e).
Proof.
  apply grammar.exp_atom_ind; intros; auto.
  - inversion H; subst. clear H.
    rewrite fold_left_outer.
    rewrite app_ass.
    constructor.
    auto.
    apply atom_plus_list_snoc; auto.
  - auto using exp_of_atom.
Qed.
End top_down.

(*
e ::= a ('+' a)*

a ::= n
    | '(' e ')'
*)

Module automaton_parser.
  Module frame.
  Inductive t :=
  | StartParen : t
  | AfterPlusParen : exp.t -> t.
  End frame.
  Import frame.

  Definition stack := list frame.t.

  Module state.
  Inductive t :=
  | Start
  | BeforePlus : exp.t -> t
  | AfterPlus : exp.t -> t.
  End state.
  Import state.

  Inductive msg :=
  | UnexpectedToken : token.t -> state.t * stack -> msg
  | UnexpectedEOF : state.t * stack -> msg.

  Definition parser : automaton.t _ token.t _ exp.t :=
    automaton.Make
      (fun s tok =>
         match s with
         | (Start, stk) =>
           match tok with
           | token.LParen => Ok (Start, StartParen :: stk)
           | token.Const n => Ok (BeforePlus (exp.Const n), stk)
           | _ => Err (UnexpectedToken tok s)
           end
         | (BeforePlus e, stk) =>
           match tok with
           | token.Plus => Ok (AfterPlus e, stk)
           | token.RParen =>
             match stk with
             | StartParen :: stk => Ok (BeforePlus e, stk)
             | AfterPlusParen e0 :: stk => Ok (BeforePlus (exp.Plus e0 e), stk)
             | _ => Err (UnexpectedToken tok s)
             end
           | _ => Err (UnexpectedToken tok s)
           end
         | (AfterPlus e, stk) =>
           match tok with
           | token.Const n => Ok (BeforePlus (exp.Plus e (exp.Const n)), stk)
           | token.LParen => Ok (Start, AfterPlusParen e :: stk)
           | _ => Err (UnexpectedToken tok s)
           end
         end)
      (fun s =>
         match s with
         | (BeforePlus e, []) => Ok e
         | _ => Err (UnexpectedEOF s)
         end).

  Definition init : state.t * stack := (Start, []).

  Eval compute in automaton.run parser (unparse side.left e12) init.
  Eval compute in automaton.run parser (unparse side.left e123l) init.
  Eval compute in automaton.run parser (unparse side.left e123r) init.

  Lemma parser_complete' :
    (forall ts e,
        top_down.exp ts e ->
        forall stk ts',
          automaton.run' parser (ts ++ ts') (Start, stk) =
          automaton.run' parser ts' (BeforePlus e, stk)) /\
    (forall ts e,
        top_down.atom ts e ->
        (forall stk ts' acc,
          automaton.run' parser (ts ++ ts') (AfterPlus acc, stk) =
          automaton.run' parser ts' (BeforePlus (exp.Plus acc e), stk)) /\
        (forall stk ts',
          automaton.run' parser (ts ++ ts') (Start, stk) =
          automaton.run' parser ts' (BeforePlus e, stk))) /\
    (forall ts l,
        top_down.atom_plus_list ts l ->
        forall stk ts' acc,
          automaton.run' parser (ts ++ ts') (BeforePlus acc, stk) =
          automaton.run' parser ts' (BeforePlus (fold_left exp.Plus l acc), stk)).
  Proof.
    apply top_down.exp_atom_atom_plus_list_ind; auto.
    - intros ts1 ts2 a l A [IHA1 IHA2] AL IHAL stk ts'.
      now rewrite app_ass, IHA2, IHAL.
    - intros ts e E IHE. split; intros; simpl; now rewrite app_ass, IHE.
    - intros ts1 ts2 a l A [IHA1 IHA2] AL IHAL stk ts' acc.
      simpl.
      now rewrite app_ass, IHA1, IHAL.
  Qed.

  Lemma parser_complete :
    forall ts e,
      top_down.exp ts e ->
      automaton.run parser ts (Start, []) = Ok e.
  Proof.
    intros.
    eapply (proj1 parser_complete') with (ts' := [])(stk := []) in H.
    unfold automaton.run.
    rewrite app_nil_r in *. simpl in *. now rewrite H.
  Qed.

  Module stack_tokens.
    Inductive t : stack -> list token.t -> Prop :=
    | Done : t [] []
    | StartParen : forall stk ts, t stk ts -> t (StartParen :: stk) (ts ++ [token.LParen])
    | AfterPlusParen : forall stk ts e ts0,
        t stk ts -> grammar.exp e ts0 ->
        t (AfterPlusParen e :: stk) (ts ++ ts0 ++ [token.Plus; token.LParen]).
    Hint Constructors t.
  End stack_tokens.

  Module state_tokens.
    Inductive t : state.t -> list token.t -> Prop :=
    | Start : t Start []
    | BeforePlus : forall e ts, grammar.exp e ts -> t (BeforePlus e) ts
    | AfterPlus : forall e ts, grammar.exp e ts -> t (AfterPlus e) (ts ++ [token.Plus]).
    Hint Constructors t.
  End state_tokens.

  Lemma parser_sound' :
    forall ts e s stk ts0 ts1,
      stack_tokens.t stk ts0 ->
      state_tokens.t s ts1 ->
      automaton.run' parser ts (s, stk) = Ok (BeforePlus e, []) ->
      grammar.exp e (ts0 ++ ts1 ++ ts).
  Proof.
    induction ts as [|t ts]; simpl; intros.
    - invc H1. invc H. invc H0. rewrite app_nil_r. auto.
    - destruct s, t; try discriminate; invc H0.
      + eapply IHts in H1; eauto.
        rewrite app_ass in *. auto.
      + eapply IHts in H1; eauto. auto.
      + destruct stk as [|f stk]; try discriminate.
        destruct f eqn:?; invc H.
        * replace (grammar.exp _ _) with
          (grammar.exp e (ts2 ++ (token.LParen :: ts1 ++ [token.RParen]) ++ ts))
            by (simpl; now rewrite !app_ass).
          eapply IHts; eauto.
        * eapply IHts in H1; eauto.
          rewrite app_ass in *. simpl in *.
          rewrite app_ass in *. auto.
      + eapply IHts in H1; eauto. rewrite app_ass in *. auto.
      + eapply IHts in H1; eauto. rewrite !app_ass in *. auto.
      + eapply IHts with (ts1 := _ ++ [_; _]) in H1; eauto.
        rewrite !app_ass in *. auto.
  Qed.

  Lemma parser_sound :
    forall ts e,
      automaton.run' parser ts (Start, []) = Ok (BeforePlus e, []) ->
      grammar.exp e ts.
  Proof.
    intros.
    eapply parser_sound' in H; eauto.
    auto.
  Qed.
End automaton_parser.
