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
open Circomlib.Mux3
open Circomlib.Sign
open Zk_sql
open Zk_ml

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
    ; mux3 (* todo *)
    ; c_sign (* todo *)
    ; split_three
    ; greater_than
    ; mod_sum_three
    ; mod_sub_three
    ; big_add
    ; big_sub
    ; c_in
    ; big_add_mod_p
    ; big_sub_mod_p
    ; escalar_product
    ; mod_prod
    ; leq
    ; geq
    ; Zk_sql.calc_total
    ; Zk_ml.is_positive ]

let path = ref "./test/codegen_results/"

let test_circuit config c =
  try codegen !path g config c
  with err -> (
    Printf.printf "=============================\n" ;
    (* print error *)
    Printf.printf "Error in %s \n" (match c with Circuit c -> c.name) ;
    (* print error *)
    match err with
    | Failure s ->
        Printf.printf "Msg: %s \n" s ;
        Printf.printf "=============================\n"
    | _ ->
        raise err )

(* circomlib *)

let _ = path := "./test/codegen_results/circomlib/"

let _ = test_circuit [] cnot

let _ = test_circuit [] cxor

let _ = test_circuit [] cand

let _ = test_circuit [] cnand

let _ = test_circuit [] cor

let _ = test_circuit [] cxor

let _ = test_circuit [] is_zero

let _ = test_circuit [] is_equal

let _ = test_circuit [("n", 200)] less_than

let _ = test_circuit [("n", 200)] greater_than

let _ = test_circuit [("n", 200)] leq

let _ = test_circuit [("n", 200)] geq

let _ = test_circuit [("n", 500)] num2bits

let _ = test_circuit [("n", 500)] bits2num

let _ = test_circuit [("n", 10)] multi_mux_1

let _ = test_circuit [("w", 20)] escalar_product

(* Bigint *)

let _ = path := "./test/codegen_results/bigint/"

let _ = test_circuit [("k", 10)] c_big_is_equal

let _ = test_circuit [("k", 10)] c_big_is_zero

let _ = test_circuit [("n", 100)] mod_sub_three

let _ = test_circuit [("n", 100)] mod_sum_three

let _ = test_circuit [("n", 10)] mod_prod

let _ = test_circuit [("n", 100); ("m", 100)] split

let _ = test_circuit [("n", 100); ("m", 100); ("k", 100)] split_three

let _ = test_circuit [("n", 10); ("k", 5)] big_add

let _ = test_circuit [("n", 10); ("k", 5)] c_big_lt

let _ = test_circuit [("n", 10); ("k", 5)] big_add_mod_p

let _ = test_circuit [("n", 10); ("k", 5)] big_sub

let _ = test_circuit [("n", 10); ("k", 5)] big_sub_mod_p

let _ = test_circuit [("n", 10); ("k", 2); ("m_out", 2)] big_mult_short_long

(* hydra *)

let _ = path := "./test/codegen_results/hydra/"

let _ = test_circuit [] position_switcher

(* zk-sbt *)

let _ = path := "./test/codegen_results/zk_sbt/"

let _ = test_circuit [("valueArraySize", 10)] c_in

let _ = test_circuit [("valueArraySize", 10)] query

let _ = test_circuit [] get_val_by_idx

let _ = test_circuit [] cut_id

let _ = test_circuit [] cut_st

(* darkforest *)

let _ = path := "./test/codegen_results/darkforest/"

let _ = test_circuit [("choices", 10)] quin_selector

let _ = test_circuit [] is_neg

(* let _ = test_circuit [("n", 10)] random *)

let _ = test_circuit [("n", 10)] Darkforest.calc_total

(* zk-sql *)

let _ = path := "./test/codegen_results/zk_sql/"

let _ = test_circuit [("n", 10)] Zk_sql.calc_total

let _ = test_circuit [("n", 10)] Zk_sql.sum_equals

let _ = test_circuit [] Zk_sql.is_not_zero

let _ = test_circuit [] Zk_sql.is_filtered

(* zk-ml *)

let _ = path := "./test/codegen_results/zk_ml/"

let _ = test_circuit [] Zk_ml.is_negative

let _ = test_circuit [] Zk_ml.is_positive

let _ = test_circuit [] Zk_ml.relu

let _ = test_circuit [("n", 10)] Zk_ml.poly
