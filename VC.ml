let rec pp_list p oc l =
  match l with
  | [] -> ()
  | [x] -> Printf.fprintf oc "%a" p x
  | x :: xs -> Printf.fprintf oc "%a" p x; pp_list p oc xs

module Logic =
struct
  type sort = Bool | Int | UserDeclaredSort of string

  let pp_sort oc s =
    Printf.fprintf oc "%s"
                   (match s with
                    | Bool -> "Bool"
                    | Int -> "Int"
                    | UserDeclaredSort s -> s)

  type quantifier = Forall | Exists

  type expr = Var of string
            | App of string * expr list
            | Quant of quantifier * (string * sort) list * expr
            | Let of (string * expr) list * expr
            | LitInt of int
            | LitBool of bool

  let not x = App ("not", [x])
  let andd x = App ("and", x)
  let imp x y = App ("=>", [x; y])
  let forall bs e = Quant (Forall, bs, e)

  let fresh_int =
    let n = ref 0 in
    fun () -> n := n + 1; !n

  let fresh_var () =
    "fresh$" ^ string_of_int (fresh_int ())

  let is_blocked_by bs (x, e) =
    List.exists (fun (y, _) -> x = y) bs

  let drop_blocked_subst vs bs =
    List.filter (is_blocked_by bs) vs

  let rec is_free_in x e =
    match e with
    | Var y -> x = y
    | App (_, es) -> List.exists (is_free_in x) es
    | Quant (q, bs, e) ->
       List.all (fun (y, _) -> x <> y) bs && is_free_in x e
    | Let (defs, e) ->
       List.all (fun (y, _) -> x <> y) defs && is_free_in x e
    | LitInt _ | LitBool _ -> false

  let rec uncapture_binding vs (x, a) =
    match vs with
    | [] -> (x, a)
    | (y, e) :: vs -> if is_free_in x e then (fresh_var (), a)
                      else uncapture_binding vs (x, a)

  let uncapture_bindings vs bs = List.map (uncapture_binding vs) bs

  let rec subst vs e =
    match e with
    | Var s -> try List.assoc s vs
               with Not_found -> e
    | App (s, es) -> App (s, List.map (subst vs) es)
    | Quant (q, bs, e) ->
       let vs' = drop_blocked_subst vs bs in
       let bs' = uncapture_bindings vs' bs in
       let renaming = List.map (fun ((b, _), (b', _)) -> (b, Var b')) (List.combine bs bs') in
       Quant (q, bs', subst vs' (subst renaming e))
    | Let (defs, e) ->
       let vs' = drop_blocked_subst vs defs in
       let defs' = uncapture_bindings vs' defs in
       let renaming = List.map (fun ((b, _), (b', _)) -> (b, Var b')) (List.combine defs defs') in
       Let (List.map (fun (x, e) -> (x, subst vs e)) defs',
            subst vs' (subst renaming e))
    | LitInt n -> LitInt n
    | LitBool b -> LitBool b


  type rank = sort list * sort

  let pp_rank oc (args, ret) =
    Printf.fprintf oc "(%a) %a" (pp_list pp_sort) args pp_sort ret

  type sat_result = SAT | UNSAT | UNKNOWN

  let pp_quant oc q =
    Printf.fprintf oc "%s"
                   (match q with
                    | Forall -> "forall"
                    | Exists -> "exists")

  let pp_bound oc (nm, sort) = Printf.fprintf oc "(%s %a)" nm pp_sort sort

  let pp_bounds = pp_list pp_bound

  let rec pp_expr oc e =
    match e with
    | Var s -> Printf.fprintf oc "%s" s
    | App (s, es) -> Printf.fprintf oc "(%s %a)" s (pp_list pp_expr) es
    | Quant (q, bs, e) -> Printf.fprintf oc "(%a (%a) %a)"
                                         pp_quant q
                                         pp_bounds bs
                                         pp_expr e
    | Let (defs, e) -> Printf.fprintf oc "(let (%a) %a)" pp_defs defs pp_expr e
    | LitInt n -> Printf.fprintf oc "%d" n
    | LitBool b -> Printf.fprintf oc "%B" b
    and pp_defs oc defs = pp_list pp_def oc defs
    and pp_def oc (nm, e) = Printf.fprintf oc "(%s %a)" nm pp_expr e
end

module type MONAD =
sig
  type 'a t

  val ret : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end

module MonadUtils(M : MONAD) =
struct
  let rec mapM f l =
    match l with
    | [] -> M.ret []
    | x :: xs -> M.bind (f x) (fun y ->
                 M.bind (mapM f xs) (fun ys ->
                 M.ret (y :: ys)))
end

module type Solver =
sig
  open Logic

  type 'a t

  val ret : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t

  val push : unit t
  val pop : unit t

  val assrt : expr -> unit t
  val declare_sort : string -> unit t
  val declare_fun : string -> rank -> unit t

  val check_sat : sat_result t
end

module SMT2Solver : Solver =
struct
  open Logic

  type proc = { solver_input: out_channel; solver_output: in_channel }

  type 'a t = proc -> 'a

  let ret x p = x
  let bind m f p = f (m p) p

  let push p = output_string p.solver_input "(push)\n"
  let pop p = output_string p.solver_input "(pop)\n"

  let assrt e p = Printf.fprintf p.solver_input "(assert %a)\n" pp_expr e
  let declare_sort s p = Printf.fprintf p.solver_input "(declare-sort %s 0)\n" s
  let declare_fun s r p = Printf.fprintf p.solver_input "(declare-fun %s %a)\n" s pp_rank r

  let check_sat p =
    Printf.fprintf p.solver_input "(check-sat)\n%!";
    match input_line p.solver_output with
    | "sat" -> SAT
    | "unsat" -> UNSAT
    | "unknown" -> UNKNOWN
    | s -> failwith (Printf.sprintf "check_sat unexpected result %s" s)

  let run m =
    let (i, o) = Unix.open_process "z3 -stm2 -in" in
    m { solver_input = o; solver_output = i }

end

module IVL =
struct
  type quantifier = Logic.quantifier

  type binop = Plus | Sub | Mult | Div | Mod | And | Or | Imp | Iff
  type unop = Neg
  type lit = LitBool of bool | LitInt of int

  type ty = Bool | Int | UserDeclaredType of string | Map of ty list * ty

  type idtype = { name: string; ty: ty }

  type expr = Binop of binop * expr * expr
            | Unop of unop * expr
            | Literal of lit
            | Var of string
            | Select of expr * expr list
            | Store of expr * expr list * expr
            | App of string * expr list
            | Old of expr
            | Quant of quantifier * idtype list * expr

  type const = idtype
  type vardecl = idtype
  type func = string * ty list * ty
  type ax = expr
  type sign = { ins: idtype list; outs: idtype list }
  type spec = { requires: expr; modifies: string list; ensures: expr }
  type proc = { name: string; sign: sign; spec: spec }
  type stmt = Assert of expr
            | Assume of expr
            | Havoc of string list
            | Assign of string list * expr list
            | AssignMap of string * expr list * expr
            | While of expr * expr * stmt
            | If of expr * stmt * stmt
            | Call of string list * string * expr list
            | Sequence of stmt list
            | Choice of stmt list
            | Block of block
  and block = { vars: vardecl list; body: stmt }

  type impl = { name: string; sign: sign; body: block }

  type decl = TyDecl of string
            | Constant of const
            | Function of func
            | Axiom of ax
            | VarDecl of vardecl
            | Procedure of proc
            | Implementation of impl

  type program = decl list

  module MS = MonadUtils(SMT2Solver)
  open MS

  let tr_ty ty =
    match ty with
    | Bool -> Logic.Bool
    | Int -> Logic.Int
    | UserDeclaredType s -> Logic.UserDeclaredSort s
    | Map (args, ret) -> failwith "tr_ty map"

  let tr_binop op =
    match op with
    | Plus -> "+"
    | Sub -> "-"
    | Mult -> "*"
    | Div -> "div"
    | Mod -> "mod"
    | And -> "and"
    | Or -> "or"
    | Imp -> "=>"
    | Iff -> "="

  let tr_unop op =
    match op with
    | Neg -> "-"

  let tr_lit lit =
    match lit with
    | LitBool b -> Logic.LitBool b
    | LitInt n -> Logic.LitInt n

  let rec tr_expr e =
    match e with
    | Binop (op, e1, e2) -> Logic.App (tr_binop op, [tr_expr e1; tr_expr e2])
    | Unop (op, e) -> Logic.App (tr_unop op, [tr_expr e])
    | Literal lit -> tr_lit lit
    | Var s -> Logic.Var s
    | Select _ | Store _ -> failwith "tr_expr select/store"
    | App (s, es) -> Logic.App (s, List.map tr_expr es)
    | Old _ -> failwith "tr_expr old"
    | Quant (q, bs, e) -> Logic.Quant (q, List.map (fun {name; ty} -> (name, tr_ty ty)) bs,
                                       tr_expr e)

  let rec lookup_var program v =
    match program with
    | [] -> failwith "unbound variable v"
    | VarDecl {name; ty} :: xs -> if name = v then ty else lookup_var xs v
    | _ :: xs -> lookup_var xs v


  let rec wp program stmt q =
    match stmt with
    | Assert e -> Logic.andd [tr_expr e; q]
    | Assume e -> Logic.imp (tr_expr e) q
    | Havoc vs ->
       let sorts = List.map (fun v -> tr_ty (lookup_var program v)) vs in
       Logic.forall (List.combine vs sorts) q

    | Assign (vs, es) -> subst (List.combine vs es) q
    | AssignMap (_, _, _) -> failwith "wp assignmap"
    | _ -> failwith "wp fall through"
(*    | While of expr * expr * stmt
    | If of expr * stmt * stmt
    | Call of string list * string * expr list
    | Sequence of stmt list
    | Choice of stmt list
    | Block of block *)
  and wp_block program {vars; body} = failwith "wp_block";;

  let impl_vc program {name, {ins, outs}, body} =
    let {_, _, {requires, _, ensures}} = lookup_proc program name in
    let stmt = Block { vars = ins @ outs;
                       body = Sequence [Assume requires; body; Assert ensures] } in
    wp program stmt;;


  let decl_vc p d =
    match d with
    | TyDecl s -> SMT2Solver.declare_sort s
    | Constant {name; ty} -> SMT2Solver.declare_fun name ([], tr_ty ty)
    | Function (nm, args, ret) ->
       SMT2Solver.declare_fun nm (List.map tr_ty args, tr_ty ret)
    | Axiom e -> SMT2Solver.assrt (tr_expr e)
    | VarDecl _ -> SMT2Solver.ret ()
    | Procedure _ -> SMT2Solver.ret()
    | Implementation i ->
       SMT2Solver.bind SMT2Solver.push (fun _ ->
       SMT2Solver.bind (SMT2Solver.assrt (Logic.not (impl_vc p i))) (fun _ ->
       SMT2Solver.bind SMT2Solver.check_sat (fun res ->
       SMT2Solver.pop)))

  let prog_vc p = mapM (decl_vc p) p
end
