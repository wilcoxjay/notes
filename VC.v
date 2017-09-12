Require String Ensembles.
Require Import ZArith List.
Import ListNotations.

Set Implicit Arguments.

Module Type SET.
  Parameter t : Type -> Type.
  Parameter empty : forall A, t A.
  Parameter full : forall A, t A.
  Parameter singleton : forall A, A -> t A.
  Parameter union : forall A, t A -> t A -> t A.
  Parameter intersect : forall A, t A -> t A -> t A.
  Parameter big_union : forall A B, t A -> (A -> t B) -> t B.
  Parameter guard : forall A, t A -> (A -> Prop) -> t A.
  Parameter prod : forall A B, t A -> t B -> t (A * B).
End SET.

Module set : SET.
  Definition t (A : Type) := Ensembles.Ensemble A.

  Definition empty {A : Type} : t A := fun a => False.

  Definition full {A : Type} : t A := fun a => True.

  Definition singleton (A : Type) (x : A) : set.t A := fun y => x = y.

  Definition union (A : Type) (s1 s2 : t A) : t A :=
    fun a => s1 a \/ s2 a.

  Definition intersect (A : Type) (s1 s2 : t A) : t A :=
    fun a => s1 a \/ s2 a.

  Definition big_union (A B : Type) (m : t A) (f : A -> t B) : t B :=
    fun b => exists a, m a /\ f a b.

  Definition guard (A : Type) (s : t A) (p : A -> Prop) : t A :=
    intersect s p.

  Definition prod (A B : Type) (s1 : t A) (s2 : t B) : t (A * B) :=
    fun p => let '(a, b) := p in s1 a /\ s2 b.
End set.
Arguments set.full {_}.


Module symbol.
  Definition t := String.string.

  Definition eq (s1 s2 : t) : {s1 = s2} + {s1 <> s2} := String.string_dec s1 s2.
End symbol.

Module FOL.

Module arity.
  Definition t := nat.
End arity.

Module sort.
  Inductive t :=
  | Int
  | Bool
  | UserDeclaredSort : symbol.t -> t
  .

  Definition eq_dec (x y : t) : {x = y} + {x <> y}.
    refine match x, y with
           | Int, Int => left _
           | Bool, Bool => left _
           | UserDeclaredSort s1, UserDeclaredSort s2 =>
             match symbol.eq s1 s2 with
             | left pf => left _
             | right pf => right _
             end
           | _, _ => right _
           end; congruence.
  Defined.
End sort.

Module rank.
  Definition t : Type := list sort.t * sort.t.
End rank.

Module expr.
  Inductive q := Forall | Exists.

  Section expr.
    Local Unset Elimination Schemes.

    Inductive t : Type :=
    | Symbol : symbol.t -> t
    | App : symbol.t -> list t -> t
    | Quantifier : q -> list (symbol.t * sort.t) -> t -> t
    | Let : list (symbol.t * t) -> t -> t
    | Num : Z -> t
    | Bool : bool -> t
    .
  End expr.
End expr.

Inductive check_sat_response := SAT | UNSAT | UNKNOWN.

Module declaration.
  Inductive t :=
  | Fun : symbol.t -> list sort.t -> sort.t -> t
  | Sort : symbol.t -> arity.t -> t
  .

  Definition find_sort (d : t) (s : symbol.t) : option arity.t :=
    match d with
    | Fun _ _ _ => None
    | Sort s' a =>
      if symbol.eq s s'
      then Some a
      else None
    end.

  Definition find_sym (d : t) (s : symbol.t) : option rank.t :=
    match d with
    | Fun s' args ret =>
      if symbol.eq s s'
      then Some (args, ret)
      else None
    | Sort _ _ => None
    end.
End declaration.

Module assertion.
  Inductive t :=
  | Formula : expr.t -> t
  | Declaration : declaration.t -> t
  .

  Definition find_sort (a : t) (s : symbol.t) : option arity.t :=
    match a with
    | Formula _ => None
    | Declaration d =>
      declaration.find_sort d s
    end.

  Definition find_sym (a : t) (s : symbol.t) : option rank.t :=
    match a with
    | Formula _ => None
    | Declaration d =>
      declaration.find_sym d s
    end.

End assertion.

Module level.
  (* stored in reverse *)
  Definition t := list assertion.t.

  Definition assert (e : expr.t) (l : t) : t :=
    assertion.Formula e :: l.

  Definition declare (d : declaration.t) (l : t) : t :=
    assertion.Declaration d :: l.

  Definition declare_bound (l : list (symbol.t * sort.t)) (s : t) : t :=
    List.rev (List.map (fun p => let '(sym, s) := p in
                              assertion.Declaration (declaration.Fun sym [] s)) l) ++ s.

  Fixpoint find_sort (l : t) (s : symbol.t) : option arity.t :=
    match l with
    | [] => None
    | x :: l =>
      match assertion.find_sort x s with
      | None => find_sort l s
      | Some a => Some a
      end
    end.

  Fixpoint find_sym (l : t) (s : symbol.t) : option rank.t :=
    match l with
    | [] => None
    | x :: l =>
      match assertion.find_sym x s with
      | None => find_sym l s
      | Some x => Some x
      end
    end.
End level.

Module stack.
  Inductive t :=
  | Base : level.t -> t
  | Level : level.t -> t -> t
  .

  Definition transform_top_level (f : level.t -> level.t) (s : t) : t :=
    match s with
    | Base l => Base (f l)
    | Level l s => Level (f l) s
    end.

  Definition assert (e : expr.t) (s : t) : t :=
    transform_top_level (level.assert e) s.

  Definition declare (d : declaration.t) (s : t) : t :=
    transform_top_level (level.declare d) s.

  Definition declare_bound (l : list (symbol.t * sort.t)) (s : t) : t :=
    transform_top_level (level.declare_bound l) s.

  Fixpoint find_sort (stk : t) (sym : symbol.t) : option arity.t :=
    match stk with
    | Base l => level.find_sort l sym
    | Level l stk =>
      match level.find_sort l sym with
      | None => find_sort stk sym
      | Some a => Some a
      end
    end.

  Fixpoint find_sym (stk : t) (sym : symbol.t) : option rank.t :=
    match stk with
    | Base l => level.find_sym l sym
    | Level l stk =>
      match level.find_sym l sym with
      | None => find_sym stk sym
      | Some s => Some s
      end
    end.

End stack.

Module sort_wf.
  Definition p (stk : stack.t) (sym : sort.t) : bool :=
    match sym with
    | sort.Int => true
    | sort.Bool => true
    | sort.UserDeclaredSort sym =>
      match stack.find_sort stk sym with
      | None => false
      | Some a => Nat.eqb a 0
      end
    end.
End sort_wf.

Module expr_sort.
  Fixpoint f (stk : stack.t) (e : expr.t) {struct e} : option sort.t :=
    let fix f_list (stk : stack.t) (l : list expr.t) {struct l} : option (list sort.t) :=
        match l with
        | [] => Some []
        | x :: xs =>
          match f stk x with
          | None => None
          | Some y =>
            match f_list stk xs with
            | None => None
            | Some ys => Some (y :: ys)
            end
          end
        end
    in
    let fix f_let (stk : stack.t) (l : list (symbol.t * expr.t)) : option (list (symbol.t * sort.t)) :=
        match l with
        | [] => Some []
        | (sym, e) :: xs =>
          match f stk e with
          | None => None
          | Some y =>
            match f_let stk xs with
            | None => None
            | Some ys => Some ((sym, y) :: ys)
            end
          end
        end
    in
    match e with
    | expr.Symbol sym =>
      match stack.find_sym stk sym with
      | Some ([], s) => Some s
      | _ => None
      end
    | expr.App sym args =>
      match stack.find_sym stk sym with
      | None => None
      | Some (arg_tys, ret_ty) =>
        match f_list stk args with
        | None => None
        | Some ys => if list_eq_dec sort.eq_dec arg_tys ys then Some ret_ty else None
        end
      end
    | expr.Quantifier q bs e =>
      match f (stack.declare_bound bs stk) e with
      | Some sort.Bool => Some sort.Bool
      | _ => None
      end
    | expr.Let bs e =>
      match f_let stk bs with
      | None => None
      | Some cs => f (stack.declare_bound cs stk) e
      end
    | expr.Num _ => Some sort.Int
    | expr.Bool _ => Some sort.Bool
    end.
End expr_sort.

Module model.
  Axiom t : Type.
  Axiom satisfies : t -> stack.t -> Prop.
End model.

Module Type Solver.
  Parameter t : Type -> Type.

  Parameter ret : forall {A : Type}, A -> t A.
  Parameter bind : forall {A B : Type}, t A -> (A -> t B) -> t B.

  Parameter assert : expr.t -> t unit.
  Parameter declare_fun : symbol.t -> list sort.t -> sort.t -> t unit.
  Parameter declare_sort : symbol.t -> arity.t -> t unit.

  Parameter check_sat : t check_sat_response.
  Parameter push : t unit.
  Parameter pop : t unit.

  Parameter denote : forall A, t A -> stack.t -> set.t (A * stack.t).

  Parameter denote_ret : forall A (x : A) s, denote (ret x) s = set.singleton (x, s).
  Parameter denote_bind : forall A B (m : t A) (f : A -> t B) s ,
      denote (bind m f) s =
      set.big_union (denote m s) (fun p => let '(a, sa) := p in denote (f a) sa).

  Parameter denote_assert : forall e s,
      expr_sort.f s e = Some sort.Bool ->
      denote (assert e) s = set.singleton (tt, stack.assert e s).

  Parameter denote_declare_fun : forall nm arg_sorts ret_sort s,
      List.forallb (sort_wf.p s) arg_sorts = true ->
      sort_wf.p s ret_sort = true ->
      denote (declare_fun nm arg_sorts ret_sort) s =
      set.singleton (tt, stack.declare (declaration.Fun nm arg_sorts ret_sort) s).

  Parameter denote_declare_sort : forall nm a s,
      denote (declare_sort nm a) s =
      set.singleton (tt, stack.declare (declaration.Sort nm a) s).

  Parameter denote_check_sat : forall s,
      denote check_sat s =
      set.guard (set.prod set.full (set.singleton s))
                (fun r => match fst r with
                       | SAT => exists m, model.satisfies m s
                       | UNSAT => forall m, ~ model.satisfies m s
                       | UNKNOWN => True
                       end).
End Solver.

End FOL.


Fixpoint assoc {A B} (A_eq : forall x y, {x = y} + {x <> y}) (l : list (A * B)) (a : A) : option B :=
  match l with
  | [] => None
  | (k,v) :: xs => if A_eq a k then Some v else assoc A_eq xs a
  end.

Module IVL.
  Module expr.
    Inductive t :=
    | Var : symbol.t -> t
    | App : symbol.t -> list t -> t
    | Old : t -> t
    | Num : Z -> t
    | Bool : bool -> t
    | Select : t -> list t -> t 
    | Store : t -> list t -> t -> t
    | Not : t -> t
    .

    Fixpoint subst (vs : list (symbol.t * expr.t)) (e : t) : t :=
      match e with
      | Var x => match assoc symbol.eq vs x with
                | None => e
                | Some y => y
                end
      | App name l => App name (List.map (subst vs) l)
      | Old e => Old (subst vs e)
      | Num n => Num n
      | Bool b => Bool b
      | Select m l => Select (subst vs m) (List.map (subst vs) l)
      | Store m l e => Store m (List.map (subst vs) l) (subst vs e)
      | Not e => Not (subst vs e)
      end.

    Fixpoint replace_old (vs : list (symbol.t * symbol.t)) (in_old : bool) (e : t) : t :=
      match e with
      | Var x => if in_old then
                  match assoc symbol.eq vs x with
                  | None => e
                  | Some y => Var y
                  end
                else
                  e
      | App name l => App name (List.map (replace_old vs in_old) l)
      | Old e => replace_old vs true e
      | Num n => Num n
      | Bool b => Bool b
      | Select m l => Select (replace_old vs in_old m)
                            (List.map (replace_old vs in_old) l)
      | Store m l e => Store (replace_old vs in_old m)
                            (List.map (replace_old vs in_old) l)
                            (replace_old vs in_old e)
      | Not e => Not (replace_old vs in_old e)
      end.
  End expr.
  Coercion expr.Bool : bool >-> expr.t.

  Module type.
    Inductive t :=
    | Bool
    | Int
    | UserDeclaredType : symbol.t -> t
    | Map : t -> t
    .
  End type.

  Module basic_stmt.
    Inductive t :=
    | Assign : list symbol.t -> list expr.t -> t
    | Havoc : list symbol.t -> t
    | Assert : expr.t -> t
    | Assume : expr.t -> t
    | Sequence : list t -> t
    | Choice : list t -> t
    | Block : list symbol.t -> t -> t
    .

    Fixpoint remove_all (A : Type) (A_eq : forall x y : A, {x = y} + {x <> y})
             (to_remove : list A) (from : list A) : list A :=
      match to_remove with
      | [] => from
      | x :: xs => remove_all A_eq xs (remove A_eq x from)
      end.

    Fixpoint syntactic_assignment_targets (s : t) : list symbol.t :=
      let fix go_list (l : list t) : list symbol.t :=
          match l with
          | [] => []
          | s :: l => syntactic_assignment_targets s ++ go_list l
          end
      in
      match s with
      | Assign l _ => l
      | Havoc _ => []
      | Assert _ => []
      | Assume _ => []
      | Sequence l | Choice l => nodup symbol.eq (go_list l)
      | Block vars s => remove_all symbol.eq vars (syntactic_assignment_targets s)
      end.

  End basic_stmt.

  Module invariant.
    Notation t := expr.t (only parsing).
  End invariant.

  Module modifies.
    Notation t := (list symbol.t) (only parsing).
  End modifies.

  Module no_call_stmt.
    Import basic_stmt.

    Inductive t :=
    | Basic : basic_stmt.t -> t
    | MapAssign : symbol.t -> list expr.t -> expr.t -> t
    | If : expr.t -> t -> t -> t
    | While : expr.t -> invariant.t -> modifies.t -> t -> t
    .

    Fixpoint desugar (s : t) : basic_stmt.t :=
      match s with
      | Basic b => b
      | MapAssign x es e => Assign [x] [expr.Store (expr.Var x) es e]
      | If e s1 s2 => Choice [Sequence [Assume e; desugar s1];
                             Sequence [Assume (expr.Not e); desugar s2]]
      | While e inv m s =>
        Sequence [Assert inv; Havoc m; Assume inv;
                  Choice [Sequence [Assume e; desugar s; Assert inv; Assume false];
                          Sequence [Assume (expr.Not e)]]]
      end.
  End no_call_stmt.

  Module stmt.
    Inductive t :=
    | NoCall : no_call_stmt.t -> t
    | Call : list symbol.t -> symbol.t -> list expr.t -> t
    .
  End stmt.

  Module spec.
    Record t := Make {
      pre : expr.t;
      modifies : list symbol.t;
      post : expr.t
    }.
  End spec.

  Module proc.
    Record t := Make {
      name : symbol.t;
      ins : list (symbol.t * type.t);
      outs : list (symbol.t * type.t);
      spec : spec.t
    }.
  End proc.

  Module impl.
    Record t := Make {
      name : symbol.t;
      body : stmt.t
    }.
  End impl.

  Module declaration.
    Inductive t :=
    | Ty : symbol.t -> t
    | Const : symbol.t -> t
    | Fun : symbol.t -> list type.t -> type.t -> t
    | Ax : expr.t -> t
    | Proc : proc.t -> t
    | Impl : impl.t -> t
    .

    Axiom find_proc : list declaration.t -> symbol.t -> option proc.t.
  End declaration.

  Definition fresh_var (suff : String.string) (sym : symbol.t) : symbol.t :=
    String.append sym suff.

  Definition fresh_vars (suff : String.string) (l : list symbol.t) : list symbol.t :=
    map (fresh_var suff) l.

  Open Scope string_scope.

  Fixpoint stmt_desugar (ds : list declaration.t) (s : stmt.t) : option basic_stmt.t :=
    match s with
    | stmt.NoCall n => Some (no_call_stmt.desugar n)
    | stmt.Call call_outs name args =>
      match declaration.find_proc ds name with
      | None => None
      | Some p =>
        let spec := proc.spec p in
        let ins := List.map fst (proc.ins p) in
        let mods := spec.modifies spec in
        let proc_outs := List.map fst (proc.outs p) in

        let arg_vars := fresh_vars "$arg" ins in
        let old_vars := fresh_vars "$old" mods in
        let out_vars := fresh_vars "$out" proc_outs in
        Some (basic_stmt.Block (arg_vars ++ old_vars ++ out_vars)
          (basic_stmt.Sequence [
               basic_stmt.Assign arg_vars args;
               basic_stmt.Assert (expr.subst (combine ins (List.map expr.Var arg_vars))
                                             (spec.pre spec));
               basic_stmt.Assign old_vars (List.map expr.Var mods);
               basic_stmt.Havoc mods;
               basic_stmt.Assume (expr.replace_old (combine mods old_vars)
                                                   false
                                                   (spec.post spec));
               basic_stmt.Assign call_outs (List.map expr.Var out_vars)]))
      end
    end.
End IVL.