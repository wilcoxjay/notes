let argmax (f : int -> float) (l : int list) : int =
  let rec go (max_i, max) = function
    | [] -> max_i
    | x :: xs -> go (let fx = f x in if fx > max then (x, fx) else (max_i, max)) xs
  in match l with
     | [] -> raise Not_found
     | x :: xs -> go (x, f x) xs

let absf a = if a < 0.0 then -. a else a

let range lo hi =
  let rec go acc x =
    if x < lo then acc
    else go (x :: acc) (x - 1)
  in go [] (hi - 1)

let near_zero x = x = 0.0

let rec transpose = function
| [] -> []
| [] :: xss -> transpose xss
| (x::xs) :: xss ->
   (x :: List.map List.hd xss) :: transpose (xs :: List.map List.tl xss)


module Matrix : sig
  type t
  exception Singular of int * int

  val of_list : float list list -> t
  val to_list : t -> float list list
  val print : t -> unit
  val gaussian_elim : t -> unit
  val get : t -> int -> int -> float
end
=
struct

type t = { buf: float array array; inner_dim: int }

let of_list l =
  let buf = Array.of_list (List.map Array.of_list l) in
  { buf = buf; inner_dim = if Array.length buf > 0 then Array.length buf.(0) else 0 }

let to_list m =
  List.map Array.to_list (Array.to_list m.buf)

let print m =
  let print_row r =
    for i = 0 to m.inner_dim - 1 do
      if i > 0 then print_string " " else ();
      Printf.printf "%g" r.(i)
    done
  in
  for i = 0 to Array.length m.buf - 1 do
    print_row m.buf.(i);
    print_newline ()
  done

let swap_rows m i j =
  let t = m.buf.(i) in
  m.buf.(i) <- m.buf.(j);
  m.buf.(j) <- t

let add_scaled_row m dst src alpha =
  let r_dst = m.buf.(dst) in
  let r_src = m.buf.(src) in
  for j = 0 to m.inner_dim - 1 do
    r_dst.(j) <- r_dst.(j) +. alpha *. r_src.(j)
  done

let get m i j = m.buf.(i).(j)

let set m i j x = m.buf.(i).(j) <- x

exception Singular of int * int

(* transcribed from https://en.wikipedia.org/wiki/Gaussian_elimination#Pseudocode *)
let gaussian_elim mat =
  let m = Array.length mat.buf in
  let n = mat.inner_dim in
  for k = 0 to min m n - 1 do
    let i_max = argmax (fun i -> absf (get mat i k)) (range k m) in
    if near_zero (get mat i_max k)
    then raise (Singular (i_max, k))
    else swap_rows mat k i_max;
    for i = k + 1 to m - 1 do
      let f = get mat i k /. get mat k k in
      add_scaled_row mat i k (-. f)
    done
  done
end

type point = float * float * float
type line = point * point

let point_scale alpha (x,y,z) = (alpha *. x, alpha *. y, alpha *. z)
let point_add (x0,y0,z0) (x1,y1,z1) = (x0 +. x1, y0 +. y1, z0 +. z1)
let point_subtract (x0,y0,z0) (x1,y1,z1) = (x0 -. x1, y0 -. y1, z0 -. z1)

type isect_ll_result = None | Over | Cross of point

(* this actually only handles the skew case properly, I think *)
let isect_ll (p0, q0) (p1, q1) =
  let v0 = point_subtract q0 p0 in
  let v1 = point_subtract q1 p1 in
  let p = point_subtract p1 p0 in
  let triple_list (x, y, z) = [x; y; z] in
  let m = Matrix.of_list (transpose (List.map triple_list [v0; v1; p])) in
  try Matrix.gaussian_elim m; None
  with Matrix.Singular (i, j) as e ->
      (* we expect the augmented exception since the system is overdetermined *)
      if i != 2 || j != 2
      then raise e
      else
        (* backsolve *)
        let t1 = Matrix.get m 1 2 /. Matrix.get m 1 1 in
        (* we could also express the intersection point in terms of the first line,
           but we don't care since we only need one expression for it. *)
        (* let t0 = (Matrix.get m 0 2 -. Matrix.get m 0 1 *. t1) /. Matrix.get m 0 0 in *)
        Cross (point_add p1 (point_scale t1 v1))

let tests =
  [ ( ( (0.0, 0.0, 0.0)
      , (1.0, 0.0, 1.0)
      )
    , ( (0.707, 0.0, 0.707)
      , (1.414, 0.0, 0.0)
      )
    )
  ; ( ( (4.0, 7.0, 9.0)
      , (1.0, 1.0, 1.0)
      )
    , ( (0.5, 0.7, 1.0)
      , (1.0, 0.2, 9.0)
      )
    )
  ; ( ( (0.0, 0.0, 0.0)
      , (0.0, 0.0, 1.0)
      )
    , ( (0.0, 0.0, 0.0)
      , (1.0, 0.0, 1.0)
      )
    )
  ]

let run_tests () =
  List.map (fun (l0, l1) -> isect_ll l0 l1) tests

(* isect_ll l0 l1;;*)
(* ^ correctly returns (0.707, 0.0, 0.707) *)
