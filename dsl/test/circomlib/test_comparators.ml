open Core
open Circomlib.Comparators

let check_is_zero = Typecheck.typecheck_circuit [] is_zero

let _ =
  print_endline
    (Format.sprintf "Number of constraints: %d\n" (List.length check_is_zero))

let _ =
  List.iter check_is_zero ~f:(fun c ->
      print_endline @@ Typecheck.show_cons @@ c )


let _ =
  check_is_zero |> Coqgen.generate_lemmas is_zero
  |> print_endline
      
(* 
let check_is_equal =
  Typecheck.typecheck_circuit
    Typecheck.(add_to_delta d_empty is_zero)
    c_is_equal

let _ =
  print_endline
    (Format.sprintf "Number of constraints: %d\n" (List.length check_is_equal))

let _ =
  List.iter check_is_equal ~f:(fun c ->
      print_endline @@ Typecheck.show_cons @@ c ) *)
