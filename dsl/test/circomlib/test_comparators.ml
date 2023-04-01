open Core
open Circomlib.Comparators

let check_is_zero = Typecheck.typecheck_circuit [] is_zero

let _ =
  print_endline
    (Format.sprintf "Number of constraints: %d\n" (List.length check_is_zero))

let _ =
  List.iter check_is_zero ~f:(fun c ->
      print_endline @@ Typecheck.show_cons @@ c )

let _ = check_is_zero |> Coqgen.generate_lemmas is_zero |> print_endline

let check_lt =
  Typecheck.typecheck_circuit
    (Typecheck.add_to_deltas [] Circomlib.[Bitify.num2bits; Gates.cnot])
    less_than

let _ =
  print_endline
    (Format.sprintf "Number of constraints: %d\n" (List.length check_lt))

let _ =
  List.iter check_lt ~f:(fun c -> print_endline @@ Typecheck.show_cons @@ c)

let _ = check_lt |> Coqgen.generate_lemmas less_than |> print_endline
