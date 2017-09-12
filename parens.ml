(*
module PL = struct
  let Cmp
end

type pt_pred =
        | Exist of (N.t -> pt_pred * pt_pred)

let rec denote c =
    let eq n = PL.Cmp(EQ, n) in
    match c with
    | Unop (Trans delta, c') ->
       let d = denote c' in
       PL.Exist (fun x -> d, eq (N.add x delta))
 *)

let foo = (fun x -> x, x)
