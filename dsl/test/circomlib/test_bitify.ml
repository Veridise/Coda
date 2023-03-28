open Core
open Circomlib.Bitify

let check_n2b = Typecheck.typecheck_circuit [] num2bits

let check_b2n = Typecheck.typecheck_circuit [] bits2num

let spf = Format.sprintf

let pf = Printf.printf

(* let _ =
     pf "Number of constraints: %d\n" (List.length check_n2b) ;
     pf "Number of non-trivial constraints: %d\n"
       (List.length (check_n2b |> Typecheck.filter_nontrivial))

   let _ =
     check_n2b |> Typecheck.filter_nontrivial
     |> Coqgen.generate_lemmas num2bits
     |> print_endline *)

let _ =
  pf "Number of constraints: %d\n" (List.length check_b2n) ;
  pf "Number of non-trivial constraints: %d\n"
    (List.length (check_b2n |> Typecheck.filter_nontrivial))

let _ =
  check_b2n |> Typecheck.filter_nontrivial
  |> Coqgen.generate_lemmas bits2num
  |> print_endline
