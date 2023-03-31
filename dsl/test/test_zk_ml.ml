open Core
open Typecheck
open Coqgen

let d = add_to_deltas [] [Zk_ml.sign; Circomlib.Comparators.is_zero]

let d' = add_to_deltas [] [Zk_ml.is_positive]

let check_is_negative = Typecheck.typecheck_circuit d Zk_ml.is_negative

let check_is_positive = Typecheck.typecheck_circuit d Zk_ml.is_positive

let check_relu = Typecheck.typecheck_circuit d' Zk_ml.relu

let check_poly = Typecheck.typecheck_circuit [] Zk_ml.poly

let _ =
  print_endline
    (Format.sprintf "Number of constraints: %d\n" (List.length check_relu))

let _ =
  (* List.iter check_not ~f:(fun c -> print_endline @@ Typecheck.show_cons @@ c) *)
  check_poly |> filter_nontrivial |> generate_lemmas |> print_endline
