open Core
open Circomlib.Bitify

let check_all_binary = Typecheck.typecheck_circuit [] c_num2bits

let spf = Format.sprintf

let pf = Printf.printf

(* let _ = *)
(* check_all_binary |> Typecheck.pc ~filter:true *)

let _ =
  pf "Number of constraints: %d\n" (List.length check_all_binary) ;
  pf "Number of non-trivial constraints: %d\n"
    (List.length (check_all_binary |> Typecheck.filter_trivial))
