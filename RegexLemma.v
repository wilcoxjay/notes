Require Import Ascii.
Require Import String.

Open Scope string_scope.

Inductive regexp :=
 | regexp_zero : regexp
 | regexp_unit : regexp
 | regexp_char (c:ascii)
 | regexp_or (r:regexp) (r':regexp)
 | regexp_concat (r:regexp) (r':regexp)
 | regexp_star (r:regexp).

Inductive s_in_regexp_lang : string -> regexp -> Prop :=
 | s_in_regexp_lang_unit : 
     s_in_regexp_lang  ""  regexp_unit
 | s_in_regexp_lang_char : forall (a5:ascii),
     s_in_regexp_lang  (String  a5  "")  (regexp_char a5)
 | s_in_regexp_lang_or_1 : forall (s5:string) (r1 r2:regexp),
     s_in_regexp_lang s5 r1 ->
     s_in_regexp_lang s5 (regexp_or r1 r2)
 | s_in_regexp_lang_or_2 : forall (s5:string) (r1 r2:regexp),
     s_in_regexp_lang s5 r2 ->
     s_in_regexp_lang s5 (regexp_or r1 r2)
 | s_in_regexp_lang_concat : forall (s5 s':string) (r1 r2:regexp),
     s_in_regexp_lang s5 r1 ->
     s_in_regexp_lang s' r2 ->
     s_in_regexp_lang  ( s5  ++  s' )  (regexp_concat r1 r2)
 | s_in_regexp_lang_star_1 : forall (r:regexp),
     s_in_regexp_lang  ""  (regexp_star r)
 | s_in_regexp_lang_star_2 : forall (s5 s':string) (r:regexp),
     s_in_regexp_lang s5 r ->
     s_in_regexp_lang s' (regexp_star r) ->
     s_in_regexp_lang  ( s5  ++  s' )  (regexp_star r).

Lemma regexp_star_c_split : forall r' s' c,
  s_in_regexp_lang (String c s') (regexp_star r') ->
  exists s1 s2,
    s' = s1 ++ s2 /\ s_in_regexp_lang (String c s1) r' /\
    s_in_regexp_lang s2 (regexp_star r').
Proof.
  intros.
  remember (String c s') as s0. remember (regexp_star r') as r0.
  revert r' s' c Heqs0 Heqr0.
  induction H; intros; try congruence.
  inversion Heqr0; subst; clear Heqr0.
  destruct s5.
  - apply IHs_in_regexp_lang2; auto.
  - simpl in *. inversion Heqs0; subst; clear Heqs0.
    eauto.
Qed.