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
open Circomlib.Mux1
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
    ; big_lt
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

let _ = test_circuit [] cnot (* 0 + 1 = 1 *) (* 1 *)

let _ = test_circuit [] cxor (* 1 + 0 = 1 *) (* 1 *)

let _ = test_circuit [] cand (* 1 + 0 = 1 *) (* 1 *)

let _ = test_circuit [] cnand (* 1 + 0 = 1 *) (* 1 *)

let _ = test_circuit [] cor (* 1 + 0 = 1 *) (* 1 *)

let _ = test_circuit [] cnor (* 1 + 0 = 1 *) (* 1 *)

let _ = test_circuit [] is_zero (* 2 + 0 = 2 *) (* 2 *)

let _ = test_circuit [] is_equal (* 2 + 1 = 3 *) (* 3 *)

let _ = test_circuit [("n", 252)] less_than (* 253 + 3 = 256 *) (* 255 *)

let _ = test_circuit [("n", 252)] greater_than (* 253 + 3 = 256 *) (* 255 *)

let _ = test_circuit [("n", 252)] leq (* 253 + 4 = 257 *) (* 255 *)

let _ = test_circuit [("n", 252)] geq (* 253 + 4 = 257 *) (* 255 *)

let _ = test_circuit [("n", 252)] num2bits (* 252 + 1 = 253 *) (* 253 *)

let _ = test_circuit [("n", 252)] bits2num (* 0 + 1 = 1 *) (* 1 *)

let _ = test_circuit [("n", 252)] multi_mux_1 (* 252 + 0 = 252 *) (* 252 *)

let _ = test_circuit [("w", 252)] escalar_product (* 252 + 1 = 253 *) (* 253 *)

(* mux3: 8 + 1 = 9 *)

(* Bigint *)

let _ = path := "./test/codegen_results/bigint/"
(* non-linear constraints + linear constraints *)
let _ = test_circuit [("k", 6)] c_big_is_equal (* 14 + 7 = 21*) (* 15 *)

let _ = test_circuit [("k", 6)] c_big_is_zero (* 14 + 1 = 15*) (* 15 *)

let _ = test_circuit [("n", 43)] mod_sub_three (* 45 + 5 = 50*) (* 48 *)

let _ = test_circuit [("n", 43)] mod_sum_three (* 45 + 4 = 49*) (* 46 *)

let _ = test_circuit [("n", 43)] mod_prod (* 87 + 3 = 90 *) (* 89 *)

let _ = test_circuit [("n", 43); ("m", 43)] split (* 86 + 3 = 89 *) (* 89 *)

let _ = test_circuit [("n", 43); ("m", 43); ("k", 43)] split_three (* 129 + 4 = 133 *) (* 134 *)

let _ = test_circuit [("n", 43); ("k", 6)] big_add (* 269 + 23 = 292 *) (* 277 *)

let _ = test_circuit [("n", 43); ("k", 6)] big_lt (* 291 + 24 = 315 *) (* 302 *)

let _ = test_circuit [("n", 43); ("k", 6)] big_add_mod_p (* 929 + 85 = 1014 *) (* 950 *)

let _ = test_circuit [("n", 43); ("k", 6)] big_sub (* 269 + 29 = 298 *) (* 283 *)

let _ = test_circuit [("n", 43); ("k", 6)] big_sub_mod_p (* 550 + 52 = 602 *) (* 564 *)

let _ = test_circuit [("n", 43); ("k", 6); ("m_out", 2)] big_mult_short_long

(* hydra *)

let _ = path := "./test/codegen_results/hydra/"

let _ = test_circuit [] position_switcher (* 3 + 0 = 3 *) (* 3 *)

(* zk-sbt *)

let _ = path := "./test/codegen_results/zk_sbt/"

let _ = test_circuit [("valueArraySize", 64)] c_in (* 381 + 68 = 449 *) (* 383 *)

let _ = test_circuit [("valueArraySize", 64)] query (* 900 + 78 = 978 *)

let _ = test_circuit [] get_val_by_idx (* 16 + 2 = 18 *)

let _ = test_circuit [] cut_id (* 256 + 2 = 258 *) (* 258 *)

let _ = test_circuit [] cut_st (* 256 + 2 = 258 *) (* 258 *)

(* darkforest *)

let _ = path := "./test/codegen_results/darkforest/"

let _ = test_circuit [("choices", 16)] quin_selector

let _ = test_circuit [] is_neg

(* let _ = test_circuit [("n", 10)] random *)

let _ = test_circuit [("n", 40)] Darkforest.calc_total

(* zk-sql *)

let _ = path := "./test/codegen_results/zk_sql/"

let _ = test_circuit [("n", 40)] Zk_sql.calc_total

let _ = test_circuit [("n", 2)] Zk_sql.sum_equals

let _ = test_circuit [] Zk_sql.is_not_zero

let _ = test_circuit [] Zk_sql.is_filtered

(* zk-ml *)

let _ = path := "./test/codegen_results/zk_ml/"

let _ = test_circuit [] Zk_ml.is_negative

let _ = test_circuit [] Zk_ml.is_positive

let _ = test_circuit [] Zk_ml.relu

let _ = test_circuit [("n", 1000000)] Zk_ml.poly
