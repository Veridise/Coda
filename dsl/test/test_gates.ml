open Core
open Typecheck
open Coqgen

let check_not = Typecheck.typecheck_circuit [] Circomlib.Gates.cnot

let _ =
  print_endline
    (Format.sprintf "Number of constraints: %d\n" (List.length check_not))

let _ =
  List.iter check_not ~f:(fun c -> print_endline @@ Typecheck.show_cons @@ c)
