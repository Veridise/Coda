open Core
open Typecheck
open Coqgen

let d = add_to_deltas [] Circomlib.[Comparators.is_zero; Gates.cnot]

let check_is_not_zero = Typecheck.typecheck_circuit d Zk_sql.is_not_zero

let _ =
  print_endline
    (Format.sprintf "Number of constraints: %d\n"
       (List.length check_is_not_zero) )

let _ =
  (* List.iter check_not ~f:(fun c -> print_endline @@ Typecheck.show_cons @@ c) *)
  check_is_not_zero |> filter_nontrivial |> generate_lemmas |> print_endline
