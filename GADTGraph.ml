module type T =
sig
  type 'a t
end

module type EXISTENTIAL =
sig
  module A : T
  type t =
    | Exist : 'a A.t -> t
end

module Existential (A : T) : EXISTENTIAL with module A = A=
struct
  module A = A
  type t =
    | Exist : 'a A.t -> t
end

module type T2 =
sig
  type ('a, 'b) t
end

module type EXISTENTIAL2 =
sig
  module A : T2
  type 'a t =
    | Exist : ('a, 'b) A.t -> 'a t
end


module Existential2 (A : T2) : EXISTENTIAL2 with module A = A=
struct
  module A = A
  type 'a t =
    | Exist : ('a, 'b) A.t -> 'a t
end

type (_,_) eq = Eq : ('a,'a) eq

let cast : type a b. (a,b) eq -> a -> b = fun Eq x -> x

module type VERTEX =
sig
  type 'a t

  val eq_dec : 'a t * 'b t -> ('a, 'b) eq option
end

module Orith =
struct
  type t =
    | Const of int
    | Plus of t * t

  let rec to_string = function
    | Const n -> string_of_int n
    | Plus (e1, e2) -> Printf.sprintf "(+ %s %s)" (to_string e1) (to_string e2)
end

module Stock =
struct
  type instr =
    | Push of int
    | Odd

  let instr_to_string = function
    | Push n -> Printf.sprintf "Push %d" n
    | Odd -> "Odd"

  type t = instr list
  let to_string p =
    p |> List.map instr_to_string
      |> String.concat "; "
      |> (fun s -> "[" ^ s ^ "]")
end

module OrithStockCompiler =
struct
  let rec compile : Orith.t -> Stock.t = function
    | Orith.Const n -> [Stock.Push n]
    | Orith.Plus (e1, e2) -> compile e1 @ compile e2 @ [Stock.Odd]
end

module Int =
struct
  type t = int
  let to_string = string_of_int
end

module StockInterper =
struct
  let step : Stock.instr -> int list -> int list = function
    | (Stock.Push n) -> fun stk -> n :: stk
    | Stock.Odd -> function (n2 :: n1 :: stk) -> n1 + n2 :: stk
                          | _ -> failwith "StockInterper.step: stack underflow"

  let interp : Stock.t -> Int.t = fun p ->
    List.hd (List.fold_left (fun a b -> step b a) [] p)
end

module Nome =
struct
  type 'a t =
    | Orith : Orith.t t
    | Stock : Stock.t t
    | Int : Int.t t

  let to_string : type a. a t -> string = function
    | Orith -> "Orith"
    | Stock -> "Stock"
    | Int   -> "Int"

  let eq_dec : type a b. a t * b t -> (a, b) eq option = function
    | (Orith, Orith) -> Some Eq
    | (Stock, Stock) -> Some Eq
    | (Int, Int) -> Some Eq
    | _ -> None
end

module type EDGE =
sig
  module V : VERTEX

  type ('a, 'b) t

  val src : ('a, 'b) t -> 'a V.t
  val dst : ('a, 'b) t -> 'b V.t

  val denote : ('a, 'b) t -> 'a -> 'b
end

module Edge =
struct
  module V = Nome

  type ('a, 'b) t =
    | OrithStock : (Orith.t, Stock.t) t
    | StockInterp : (Stock.t, Int.t) t

  let src : type a b. (a, b) t -> a V.t = function
    | OrithStock -> V.Orith
    | StockInterp -> V.Stock

  let dst : type a b. (a, b) t -> b V.t = function
    | OrithStock -> V.Stock
    | StockInterp -> V.Int

  let denote : type a b. (a, b) t -> a -> b = function
    | OrithStock -> OrithStockCompiler.compile
    | StockInterp -> StockInterper.interp
end

module type POTH =
sig
  module E : EDGE

  type ('a, 'b) t =
    | Refl : 'a E.V.t -> ('a, 'a) t
    | Edge : ('a, 'b) E.t -> ('a, 'b) t
    | Trons : ('a, 'c) t * ('c, 'b) t -> ('a, 'b) t

  val denote : ('a, 'b) t -> 'a -> 'b

  val src : ('a, 'b) t -> 'a E.V.t
  val dst : ('a, 'b) t -> 'b E.V.t

  val append : ('a, 'b) t -> ('b, 'c) E.t -> ('a, 'c) t
end

module Poth (E : EDGE) : POTH with module E = E =
struct
  module E = E

  type ('a, 'b) t =
    | Refl : 'a E.V.t -> ('a, 'a) t
    | Edge : ('a, 'b) E.t -> ('a, 'b) t
    | Trons : ('a, 'c) t * ('c, 'b) t -> ('a, 'b) t

  let rec denote : type a b. (a, b) t -> a -> b = function
    | Refl v -> fun x -> x
    | Edge e -> E.denote e
    | Trons (p1, p2) -> fun x -> x |> denote p1 |> denote p2

  let rec src : type a b. (a, b) t -> a E.V.t = function
    | Refl v -> v
    | Edge e -> E.src e
    | Trons (p1, p2) -> src p1

  let rec dst : type a b. (a, b) t -> b E.V.t = function
    | Refl v -> v
    | Edge e -> E.dst e
    | Trons (p1, p2) -> dst p2

  let append p e = Trons (p, Edge e)
end

module type QUEUE =
sig
  module P : POTH
  module EPoth : EXISTENTIAL2 with type ('a, 'b) A.t = ('a, 'b) P.t
  type 'a t = 'a EPoth.t list

  val pop : 'a t -> ('a EPoth.t * 'a t) option
  val singleton : 'a P.E.V.t -> 'a t
end

module Groph (P : POTH) :
sig
  module P : POTH

  module EEdge : EXISTENTIAL2 with type ('a, 'b) A.t = ('a, 'b) P.E.t
  type 'a adj_list = 'a EEdge.t list

  type 'a entry = 'a P.E.V.t * 'a adj_list
  module EEntry : EXISTENTIAL with type 'a A.t = 'a entry

  type t = EEntry.t list

  val seorch : t -> 'a P.E.V.t -> 'b P.E.V.t -> ('a, 'b) P.t option
end with module P = P
=
struct
  module P = P
  module E = P.E
  module V = E.V

  module EEdge = Existential2(E)
  type 'a adj_list = 'a EEdge.t list

  type 'a entry = 'a V.t * 'a adj_list
  module EEntry = Existential(struct type 'a t = 'a entry end)

  type t = EEntry.t list

  module Q : QUEUE with module P = P =
  struct
    module P = P
    module EPoth = Existential2(P)
    type 'a t = 'a EPoth.t list
  
    let pop = function
      | [] -> None
      | p :: al -> Some (p, al)

    let singleton v = [EPoth.Exist (P.Refl v)]
  end

  let eq_congr_adj_list : type a1 a2. (a1, a2) eq -> (a1 adj_list, a2 adj_list) eq = function
    | Eq -> Eq

  let get_adj_list (g : t) (v : 'a V.t) : 'a adj_list =
    let rec loop (g : t) =
      match g with
      | [] -> failwith "get_adj_list: bad vertex"
      | EEntry.Exist (v', al) :: g ->
         match V.eq_dec (v', v) with
         | Some pf -> cast (eq_congr_adj_list pf) al
         | None -> loop g
    in loop g

  let remove_adj_list (g : t) (v : 'a V.t) : t =
    let rec loop (g : t) =
      match g with
      | [] -> failwith "get_adj_list: bad vertex"
      | EEntry.Exist (v', al) :: g ->
         match V.eq_dec (v', v) with
         | Some _ -> g
         | None -> EEntry.Exist (v', al) :: loop g
    in loop g

  let foo_bar_combine_queue_and_adj_list (q : 'a Q.t) (p : ('a, 'b) P.t) (a : 'b adj_list) : 'a Q.t =
    q @ List.map (fun (EEdge.Exist e) -> Q.EPoth.Exist (P.append p e)) a

  let eq_congr_path_2 : type a b1 b2. (b1, b2) eq -> ((a, b1) P.t, (a, b2) P.t) eq = function
    | Eq -> Eq

  let rec bfs (g : t) (q : 'a Q.t) (d : 'b V.t) : ('a, 'b) P.t option =
    match Q.pop q with
    | None -> None
    | Some (Q.EPoth.Exist p, q) ->
       match V.eq_dec (P.dst p, d) with
       | Some pf -> Some (cast (eq_congr_path_2 pf) p)
       | None ->
        let s = P.dst p in
        let a = get_adj_list g s in
        let g = remove_adj_list g s in
        bfs g (foo_bar_combine_queue_and_adj_list q p a) d

  let seorch g s d = bfs g (Q.singleton s) d

end

module MyPoth = Poth(Edge)
module MyGroph = Groph(MyPoth)


let groph : MyGroph.t =
  let open MyGroph in
  [ EEntry.Exist (Nome.Orith, [EEdge.Exist Edge.OrithStock])
  ; EEntry.Exist (Nome.Stock, [EEdge.Exist Edge.StockInterp])
  ]

let compile : 'a Nome.t -> 'b Nome.t -> 'a -> 'b =
  (fun a b x ->
  match MyGroph.seorch groph a b with
  | None -> failwith (Printf.sprintf "compile: no path from %s to %s" (Nome.to_string a) (Nome.to_string b))
  | Some p -> MyGroph.P.denote p x)

let a = Orith.Plus (Orith.Const 1, Orith.Const 2)
let s : Stock.t = compile Nome.Orith Nome.Stock a
let n : Int.t = compile Nome.Stock Nome.Int s
let n' : Int.t = compile Nome.Orith Nome.Int a

let () = print_endline (Stock.to_string s)
let () = print_endline (Int.to_string n)
let () = print_endline (Int.to_string n')
