let pass = "PASS"
let fail = "FAIL"

let print_outcome test check ans res =
  Printf.printf "  %-25s : " test;
  if check ans res
  then print_endline pass
  else print_endline fail

let print_outcome_eq test ans res =
  print_outcome test (=) ans res

type test =
  (* 'a is existentially quantified here:
     you can build a test with anything you like plugged in for 'a;
     when you pattern match on it later, you will just know that there
     is *some* type that works. *)
  | Test : string * ('a -> unit) * 'a list -> test

let run_test (t: test) =
  match t with
  | Test (nm, f, l) ->
     (* we just pattern matched on a test; we can apply f to elements of l,
        but we don't know what type the elements are (just that they are
        the same as the domain of f) *)
     [ "***"
     ; nm
     ; "tests *** \n"
     ] |> String.concat " "
       |> print_endline;
     List.iter f l;
     print_endline ""


(* Notice that foo is of type int -> int *)
let foo n = n + 1

let test_foo (nm, x, ans) =
  print_outcome_eq nm ans (foo x)

let foo_tests =
  [ ( "test001"
    , 1
    , 2
    )
  ; ( "test002"
    , 2
    , 3
    )
  ]

(* Notice that bar is of type string -> string *)
let bar s = "hello " ^ s

let test_bar (nm, s, ans) =
  print_outcome_eq nm ans (bar s)

let bar_tests =
  [ ( "test001"
    , "world"
    , "hello world"
    )
  ; ( "test002"
    , "chandra"
    , "hello chandra"
    )
  ]

let _ =
  (* Even though foo and bar have different types, we can make a list of tests. *)
  [ Test ("foo", test_foo, foo_tests)
  ; Test ("bar", test_bar, bar_tests)
  ] |>
  List.iter run_test

