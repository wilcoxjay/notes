Require Import List.
Import ListNotations.

Inductive reg_exp (T : Type) : Type :=
| EmptySet : reg_exp T
| EmptyStr : reg_exp T
| Char : T -> reg_exp T
| App : reg_exp T -> reg_exp T -> reg_exp T
| Union : reg_exp T -> reg_exp T -> reg_exp T
| Star : reg_exp T -> reg_exp T.

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar : forall x, exp_match [x] (Char x)
| MApp : forall s1 re1 s2 re2,
           exp_match s1 re1 ->
           exp_match s2 re2 ->
           exp_match (s1 ++ s2) (App re1 re2)
| MUnionL : forall s1 re1 re2,
              exp_match s1 re1 ->
              exp_match s1 (Union re1 re2)
| MUnionR : forall re1 s2 re2,
              exp_match s2 re2 ->
              exp_match s2 (Union re1 re2)
| MStar0 : forall re, exp_match [] (Star re)
| MStarApp : forall s1 s2 re,
               exp_match s1 re ->
               exp_match s2 (Star re) ->
               exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros.
  generalize dependent s1.
  induction s2; simpl; intros s1.
  - split; intros H.
    + inversion H. reflexivity.
    + subst. constructor.
  - split; intros H.
    + inversion H; subst.
      inversion H3; subst.
      simpl. f_equal.
      apply IHs2; auto.
    + subst. specialize (IHs2 s2).
      change (a :: s2) with ([a] ++ s2).
      repeat constructor.
      intuition.
Qed.

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => true
  | App re1 re2 => re_not_empty re1 && re_not_empty re2
  | Union re1 re2 => re_not_empty re1 || re_not_empty re2
  | Star re' => true
  end.


Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re.
  cut ((forall s, s =~ re -> re_not_empty re = true) /\
       (re_not_empty re = true -> exists s, s =~ re)).
  firstorder.
  split; [induction re; intros s|induction re]; simpl; intros H.
  - inversion H.
  - reflexivity.
  - reflexivity.
  - apply andb_true_intro.
    inversion H; subst; firstorder.
  - apply Bool.orb_true_intro.
    inversion H; subst; firstorder.
  - reflexivity.
  - discriminate.
  - eexists. econstructor.
  - eexists. econstructor.
  - apply Bool.andb_true_iff in H.
    destruct H as [H1 H2].
    apply IHre1 in H1.
    apply IHre2 in H2.
    destruct H1 as [s1 H1].
    destruct H2 as [s2 H2].
    exists (s1 ++ s2). constructor; auto.
  - apply Bool.orb_true_iff in H.
    destruct H; [apply IHre1 in H|apply IHre2 in H]; destruct H as [s H]; exists s;
    eauto using MUnionL, MUnionR.
  - eexists. econstructor.
Qed.