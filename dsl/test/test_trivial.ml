open Core
open Trivial

let check_all_binary = Typecheck.typecheck_circuit [] c_all_binary

let _ =
  print_endline
    (Format.sprintf "Number of constraints: %d\n"
       (List.length check_all_binary) )

let _ =
  List.iter check_all_binary ~f:(fun c ->
      print_endline @@ Typecheck.show_cons @@ c )
