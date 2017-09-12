Require Import EquivDec Arith ExtensionalMaps.

Set Implicit Arguments.

Module Type EQ.
  Parameter t : Type.
  Declare Instance eq_dec : EqDec t eq.
End EQ.

Module var : EQ.
  Definition t := nat.
  Definition eq_dec := eq_nat_dec.
End var.

Module lock : EQ.
  Definition t := nat.
  Definition eq_dec := eq_nat_dec.
End lock.

Module tid : EQ.
  Definition t := nat.
  Definition eq_dec := eq_nat_dec.
End tid.

Module Type ENV.
  Declare Module E : EQ.
  Declare Instance map : map.class E.t.
  Definition t V := @map.t E.t map V.
End ENV.

Module env (E : EQ) : ENV with Module E := E.
  Module E := E.
  Definition map : map.class E.t := funcmap.funcmap _.
  Definition t V := @map.t E.t map V.
End env.

Module varenv := env var.
Module lockenv := env lock.
Module control := env tid.

Notation mem V := (prod (varenv.t V) (lockenv.t tid.t)).

Module cmd.
  Inductive t V A :=
  | Ret (x : A)
  | Tid (k : tid.t -> t V A)
  | Read (x : var.t) (k : V -> t V A)
  | Write (x : var.t) (v : V) (k : t V A)
  | Acquire (l : lock.t) (k : t V A)
  | Release (l : lock.t) (k : t V A)
  | While (e : t V bool) (body : t V unit) (k : t V A)
  | Fork (child : tid.t(*parent*) -> t V unit) (k : tid.t(*child*) -> t V A)
  | Join (tid : tid.t) (k : t V A)
  (* | Atomic B (R : mem V -> mem V -> B -> Prop) (k : B -> t V A) *)
  .
  Arguments Ret {_} {_} _.

  Fixpoint bind V A B (c1 : t V A) (c2 : A -> t V B) : t V B :=
    match c1 with
    | Ret x => c2 x
    | Tid k => Tid (fun tid => bind (k tid) c2)
    | Read x k => Read x (fun v => bind (k v) c2)
    | Write x v k => Write x v (bind k c2)
    | Acquire l k => Acquire l (bind k c2)
    | Release l k => Release l (bind k c2)
    | While e body k => While e body (bind k c2)
    | Fork child k => Fork child (fun tid => bind (k tid) c2)
    | Join tid k => Join tid (bind k c2)
    end.
End cmd.

Notation config V := (mem V * control.t (cmd.t V unit) * bool)%type.

Module step.
  Inductive t V (tid : tid.t) : config V -> config V -> Prop :=
  | Tid : forall E L C k,
      map.get tid C = Some (cmd.Tid k) ->
      t V tid (E, L, C, true) (E, L, map.set tid (k tid) C, true)
  | Read : forall E L C x k v,
      map.get tid C = Some (cmd.Read x k) ->
      map.get x E = Some v ->
      t V tid (E, L, C, true) (E, L, map.set tid (k v) C, true)
  | ReadErr : forall E L C x k,
        map.get tid C = Some (cmd.Read x k) ->
        map.get x E = None ->
        t V tid (E, L, C, true) (E, L, C, false)
  | Write : forall E L C x v k,
      map.get tid C = Some (cmd.Write x v k) ->
      t V tid (E, L, C, true) (map.set x v E, L, map.set tid k C, true)
  | Acquire : forall E L C l k,
      map.get tid C = Some (cmd.Acquire l k) ->
      map.get l L = None ->
      t V tid (E, L, C, true) (E, map.set l tid L, map.set tid k C, true)
  | Release : forall E L C l k,
      map.get tid C = Some (cmd.Acquire l k) ->
      map.get l L = Some tid ->
      t V tid (E, L, C, true) (E, map.rem l L, map.set tid k C, true)
  | ReleaseErr : forall E L C l k,
      map.get tid C = Some (cmd.Acquire l k) ->
      map.get l L <> Some tid ->
      t V tid (E, L, C, true) (E, L, C, false)
  | While : forall E L C e body k,
      map.get tid C = Some (cmd.While e body k) ->
      let c' := cmd.bind e (fun b => if b then cmd.bind body (fun _ => cmd.While e body k)
                                  else k) in
      t V tid (E, L, C, true) (E, L, map.set tid c' C, true)
  | Fork : forall E L C child k,
      map.get tid C = Some (cmd.Fork child k) ->
      let tid' := map.fresh C in
      t V tid (E, L, C, true) (E, L, map.set tid (k tid') (map.set tid' (child tid) C), true)
  | Join : forall E L C tid' k,
      map.get tid C = Some (cmd.Join tid' k) ->
      map.get tid' C = Some (cmd.Ret tt) ->
      t V tid (E, L, C, true) (E, L, map.set tid k C, true)
  .
End step.