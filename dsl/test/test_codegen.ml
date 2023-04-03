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
open Bigint.Big_mult
open Semaphore
open Hydra
open Darkforest
open Zk_sbt

let g =
  add_to_deltas []
    [ is_zero
    ; is_equal
    ; less_than
    ; num2bits
    ; bits2num
    ; c_big_is_zero
    ; c_big_is_equal
    ; c_big_lt
    ; cand
    ; split
    ; cnot
    ; cor
    ; split_three
    ; greater_than
    ; mod_sum_three
    ; c_mod_sub_three
    ; big_add
    ; big_sub
    ; c_in
    ; big_add_mod_p
    ; big_sub_mod_p
    ; escalar_product
    ; mod_prod ]

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

let _ = test_circuit [] is_zero

let _ = test_circuit [] is_equal

let _ = test_circuit [("n", 500)] num2bits

let _ = test_circuit [("n", 500)] bits2num

let _ = test_circuit [("n", 200)] less_than

let _ = test_circuit [("n", 200)] greater_than

let _ = test_circuit [("k", 10)] c_big_is_zero

let _ = test_circuit [("n", 10); ("k", 10)] c_big_lt

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

let _ = test_circuit [("n", 10)] mod_prod

let _ = test_circuit [("n", 10); ("k", 20); ("m_out", 20)] big_mult_short_long

let _ = test_circuit [("n", 10)] multi_mux_1

let _ = test_circuit [("nLevels", 10)] mrkl_tree_incl_pf

let _ = test_circuit [] position_switcher

let _ = test_circuit [("choices", 10)] quin_selector

let _ = test_circuit [] is_neg

let _ = test_circuit [("n", 10)] calc_total

let _ = test_circuit [("n", 10)] random

let _ = test_circuit [("valueArraySize", 10)] c_in

let _ = test_circuit [("valueArraySize", 10)] query

let _ = test_circuit [] get_val_by_idx

let _ = test_circuit [] cut_id

let _ = test_circuit [] cut_st
