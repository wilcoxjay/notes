(* Yet another state-machine *)

Require Import List.
Import ListNotations.
Set Implicit Arguments.


Ltac break_match :=
  match goal with
  | [  |- context [ match ?X with _ => _ end ] ] => destruct X eqn:?
  | [ H : context [ match ?X with _ => _ end ] |- _ ] => destruct X eqn:?
  end.

Ltac invc H :=
  inversion H; subst; clear H.


Parameter byte : Type.

Inductive result S A :=
| Done (a : A)
| More (s : S)
| Error.
Arguments Done {_ _} _.
Arguments More {_ _} _.
Arguments Error {_ _}.

Module stepper.
  CoInductive t A :=
  | step : (byte -> result (t A) A) -> t A.

  Fixpoint run A (m : t A) (l : list byte) : result (t A) (A * list byte) :=
    match l with
    | [] => More m
    | b :: l =>
      match m with
      | step f =>
        match f b with
        | Done a => Done (a, l)
        | More m => run m l
        | Error => Error
        end
      end
    end.

  CoFixpoint map_result A B (f : A -> result (t B) B) (s : t A) : t B :=
    match s with
    | step g => step (fun b => match g b with
                           | Done a => f a
                           | More s => More (map_result f s)
                           | Error => Error
                           end)
    end.

  Lemma run_map_result :
    forall A B (f : A -> result (t B) B) (s : t A) l,
      run (map_result f s) l =
      match run s l with
      | Done (a, l) => match f a with
                      | Done b => Done (b, l)
                      | More m => run m l
                      | Error => Error
                      end
      | More s => More (map_result f s)
      | Error => Error
      end.
  Proof.
    intros A B f s l.
    revert s.
    induction l; simpl; intros s.
    - reflexivity.
    - destruct s.
      destruct (r a); auto.
  Qed.
End stepper.

Module machine.
  Definition t A := result (stepper.t A) A.

  Definition ret A (x : A) : t A := Done x.

  Definition bind A B (m : t A) (f : A -> t B) : t B :=
    match m with
    | Done a => f a
    | More s => More (stepper.map_result f s)
    | Error => Error
    end.

  Definition run A (m : t A) (l : list byte) : result (t A) (A * list byte) :=
    match m with
    | Done a => Done (a, l)
    | More s => match stepper.run s l with
               | Done x => Done x
               | More s => More (More s)
               | Error => Error
               end
    | Error => Error
    end.

  Lemma run_bind :
    forall A B (m : t A) (f : A -> t B) l,
      run (bind m f) l =
      match run m l with
      | Done (a, l) => run (f a) l
      | More m => More (bind m f)
      | Error => Error
      end.
  Proof.
    intros A B m f l.
    unfold bind, run.
    destruct m; auto.
    rewrite stepper.run_map_result.
    destruct (stepper.run s l); auto.
    destruct a.
    destruct (f a); auto.
  Qed.
End machine.

Module serializer.
  Definition t A := A -> list byte.
End serializer.

Module deserializer.
  Definition t A := machine.t A.
  Definition run A (m : t A) (l : list byte) : result (t A) (A * list byte) := machine.run m l.
  Definition ret A (x : A) : t A := machine.ret x.
  Definition bind A B (m : t A) (f : A -> t B) : t B := machine.bind m f.

  Lemma run_ret :
    forall A (x : A) l,
      run (ret x) l = Done (x, l).
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma run_bind :
    forall A B (m : t A) (f : A -> t B) l,
      run (bind m f) l =
      match run m l with
      | Done (a, l) => run (f a) l
      | More m => More (bind m f)
      | Error => Error
      end.
  Proof. exact machine.run_bind. Qed.

End deserializer.

Module serializable.
  Record t A :=
    Make { serialize : serializer.t A
         ; deserialize : deserializer.t A
         }.

  Definition wf A (S : t A) : Prop :=
    forall a bs,
      deserializer.run S.(deserialize) (S.(serialize) a ++ bs) = Done (a, bs).

  Definition byte : t Top.byte :=
    Make (fun b => [b]) (More (stepper.step (fun b => Done b))).

  Lemma byte_wf : wf byte.
  Proof.
    intros b bs.
    reflexivity.
  Qed.

  Definition pair A (SA : t A) B (SB : t B) : t (A * B).
    (* hey konne *)
    refine (Make _ _).
    refine (fun p => let '(a, b) := p in SA.(serialize) a ++ SB.(serialize) b).
    refine (deserializer.bind SA.(deserialize) (fun a =>
            deserializer.bind SB.(deserialize) (fun b =>
            deserializer.ret (a, b)))).
  Defined.

  Lemma pair_wf : forall A (SA : t A) B (SB : t B),
      wf SA ->
      wf SB ->
      wf (pair SA SB).
  Proof.
    unfold wf, pair.
    intros A SA B SB WFA WFB [a b] bs.
    cbn[serialize deserialize].
    rewrite app_ass.
    rewrite deserializer.run_bind.
    rewrite WFA.
    rewrite deserializer.run_bind.
    rewrite WFB.
    rewrite deserializer.run_ret.
    reflexivity.
  Qed.
End serializable.


