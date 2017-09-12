type nat = Z | S of nat

let rec inf = S inf

let rec id n =
  match n with
    Z -> Z
  | S n -> S (id n)
