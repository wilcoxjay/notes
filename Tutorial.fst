module Tutorial

open FStar.Exn
open FStar.All

type filename = string

(** [canWrite] is a function specifying whether a file [f] can be written *)
val canWrite : filename -> Tot bool
let canWrite (f:filename) =
  match f with 
    | "demo/tempfile" -> true
    | _ -> false

(** [canRead] is also a function ... *)
val canRead : filename -> Tot bool
let canRead (f:filename) =
  canWrite f               (* writeable files are also readable *)
  || f="demo/README"       (* and so is demo/README *)


val read  : f:filename{canRead f}  -> ML string
let read f  = FStar.IO.print_string ("Dummy read of file " ^ f ^ "\n"); f

val write : f:filename{canWrite f} -> string -> ML unit
let write f s = FStar.IO.print_string ("Dummy write of string " ^ s ^ " to file " ^ f ^ "\n")


let passwd : filename = "demo/password"
let readme : filename = "demo/README"
let tmp    : filename = "demo/tempfile"

val staticChecking : unit -> ML unit
let staticChecking () =
  let v1 = read tmp in
  let v2 = read readme in
  (*let v3 = read passwd in // invalid read, fails type-checking *)
  write tmp "hello!"
  (*; write passwd "junk" // invalid write , fails type-checking *)

exception InvalidRead
val checkedRead : filename -> ML string
let checkedRead f =
  if canRead f then read f else raise InvalidRead

exception InvalidWrite
val checkedWrite : filename -> string -> ML unit
let checkedWrite f s =
  if canWrite f then write f s else raise InvalidWrite




val factorial : nat -> Tot int
let rec factorial n =
  if n = 0 then 1 else op_Multiply n (factorial (n - 1))

val fact_greater_than_arg : x:nat{x > 2} -> Lemma (factorial x > x)
let rec fact_greater_than_arg x =
  match x with
  | 3 -> ()
  | _ -> fact_greater_than_arg (x - 1)

(* type list 'a =
  | Nil  : list 'a
  | Cons : hd:'a -> tl:list 'a -> list 'a *)

val length : list 'a -> Tot nat
let rec length l =
  match l with
  | [] -> 0
  | x :: xs -> 1 + length xs


val append : list 'a -> list 'a -> Tot (list 'a)
let rec append xs ys =
  match xs with
  | [] -> ys
  | x :: xs -> x :: (append xs ys)

val append_length : xs:list 'a -> ys:list 'a -> Lemma (length (append xs ys) == length xs + length ys)
let rec append_length xs ys =
  match xs with
  | [] -> ()
  | x :: xs -> append_length xs ys

val append_assoc : xs:list 'a -> ys:list 'a -> zs:list 'a -> Lemma (append (append xs ys) zs == append xs (append ys zs))
let rec append_assoc xs ys zs =
  match xs with
  | [] -> ()
  | x :: xs -> append_assoc xs ys zs

val mem : #a:eqtype -> a -> list a -> Tot bool
let rec mem #a x xs =
  match xs with
  | [] -> false
  | y :: xs -> x = y || mem x xs

val append_mem : #a:eqtype -> x:a -> xs:list a -> ys:list a -> Lemma (mem x (append xs ys) <==> mem x xs || mem x ys)
let rec append_mem #a x xs ys =
  match xs with
  | [] -> ()
  | hd :: xs -> append_mem x xs ys

val fibonacci : nat -> Tot nat
let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

val fib : nat -> nat -> n:nat -> Tot nat (decreases n)
let rec fib a b n =
  match n with
  | 0 -> a
  | _ -> fib b (a+b) (n-1)

val fib_is_ok : n:nat -> Lemma (fib 1 1 n == fibonacci n)
let fib_is_ok n =
  let rec aux (up:nat) (down:nat): Lemma (requires True) (ensures fib (fibonacci up) (fibonacci (up + 1)) down == fibonacci (up + down)) (decreases down) =
    match down with
    | 0 -> ()
    | _ -> aux (up + 1) (down - 1)
  in aux 0 n

val sorted: list int -> Tot bool
let rec sorted l = match l with
      | [] -> true
      | [x] -> true
      | x :: y :: xs -> x <= y && sorted (y :: xs)

val partition: #a:Type -> (a -> Tot bool) -> list a -> Tot (list a * list a)
let partition #a f xs =
  let rec aux (xs:list a) (acc:list a * list a): Tot (list a * list a) =
    match xs with
    | [] -> acc
    | x :: xs ->
    let yes, no = acc in
    aux xs (if f x then (x :: yes, no) else (yes, x :: no))
  in aux xs ([], [])

let rec sort l = match l with
  | [] -> []
  | pivot :: tl ->
    let hi, lo  = partition (fun x -> pivot <= x) tl in
    append (sort lo) (pivot :: sort hi)
