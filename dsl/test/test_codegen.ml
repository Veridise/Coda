open Codegen
open Circomlib.Gates
open Circomlib.Comparators
open Circomlib.Bitify
open Circomlib.Multiplexer
open Trivial
open Bigint.Big_is_zero
open Bigint.Big_is_equal
open Bigint.Big_less_than
open Bigint.Big_add
open Bigint.Big_sub
open Bigint.Split

let g =
  add_to_deltas []
    [ c_is_zero
    ; c_is_equal
    ; c_less_than
    ; c_num2bits
    ; c_big_is_zero
    ; c_big_is_equal
    ; c_big_lt
    ; split
    ; split_three
    ; mod_sum_three
    ; c_mod_sub_three
    ; big_add
    ; big_sub
    ; big_add_mod_p
    ; big_sub_mod_p
    ; escalar_product ]

let test_circuit config c =
  try codegen g config c
  with err -> (
    Printf.printf "=============================\n" ;
    (* print error *)
    Printf.printf "Error in %s \n" (match c with Circuit c -> c.name) ;
    (* print error *)
    match err with
    | Failure s ->
        Printf.printf "Error: %s \n" s ;
        Printf.printf "=============================\n"
    | _ ->
        raise err )

let _ = test_circuit [] cnot

let _ = test_circuit [] cxor

let _ = test_circuit [] cand

let _ = test_circuit [] cnand

let _ = test_circuit [] cor

let _ = test_circuit [] cxor

let _ = test_circuit [] c_is_zero

let _ = test_circuit [] c_is_equal

let _ = test_circuit [("n", 500)] c_num2bits

let _ = test_circuit [("n", 200)] c_less_than

(* let _ = test_circuit [("k", 500)] c_all_binary *)

let _ = test_circuit [("k", 10)] c_big_is_zero

let _ = test_circuit [("n", 100); ("k", 50)] c_big_lt

let _ = test_circuit [("n", 100)] mod_sum_three

let _ = test_circuit [("n", 100)] c_mod_sub_three

let _ = test_circuit [("n", 100); ("m", 100)] split

let _ = test_circuit [("n", 100); ("m", 100); ("k", 100)] split_three

(* TODO *)

let _ = test_circuit [("k", 10)] c_big_is_equal

let _ = test_circuit [("w", 50)] escalar_product

let _ = test_circuit [("n", 10); ("k", 50)] big_add

let _ = test_circuit [("n", 10); ("k", 50)] big_add_mod_p

let _ = test_circuit [("n", 10); ("k", 50)] big_sub

let _ = test_circuit [("n", 10); ("k", 50)] big_sub_mod_p
