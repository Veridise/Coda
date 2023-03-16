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

let _ = codegen [] [] cnot

let _ = codegen [] [] cxor

let _ = codegen [] [] cand

let _ = codegen [] [] cnand

let _ = codegen [] [] cor

let _ = codegen [] [] cxor

let _ = codegen [] [] c_is_zero

let _ = codegen (add_to_delta [] c_is_zero) [] c_is_equal

let _ = codegen [] [("n", 500)] c_num2bits

let _ = codegen (add_to_delta [] c_num2bits) [("n", 200)] c_less_than

let _ = codegen [] [("k", 500)] c_all_binary

let _ = codegen (add_to_delta [] c_is_zero) [("k", 500)] c_big_is_zero

let _ =
  codegen
    (add_to_deltas []
       [cor; c_is_zero; cand; c_num2bits; c_less_than; c_is_equal] )
    [("n", 100); ("k", 50)]
    c_big_lt

let _ = codegen (add_to_delta [] c_num2bits) [("n", 100)] mod_sum_three

let _ =
  codegen
    (add_to_deltas [] [c_num2bits; c_less_than])
    [("n", 100)]
    c_mod_sub_three

let _ = codegen (add_to_delta [] c_num2bits) [("n", 100); ("m", 100)] split

let _ =
  codegen
    (add_to_deltas [] [c_num2bits; split])
    [("n", 100); ("m", 100); ("k", 100)]
    split_three

(* TODO *)

(* let _ = codegen (add_to_delta [] c_is_equal) [("k", 50)] c_big_is_equal *)

(* let _ = codegen [] [("w", 50)] escalar_product *)

(* let _ = codegen (add_to_delta (add_to_delta [] mod_sum_three) c_num2bits) [("n", 10);("k", 50)] big_add *)

(* let _ = codegen (add_to_delta (add_to_delta (add_to_delta [] big_add) mod_sum_three) c_num2bits) [("n", 10);("k", 50)] big_add_mod_p *)

(* let _ = codegen (add_to_delta (add_to_delta (add_to_delta [] c_mod_sub_three) c_num2bits) c_less_than) [("n", 10);("k", 50)]big_sub *)

(* let _ = codegen (add_to_delta (add_to_delta (add_to_delta (add_to_delta [] big_sub) c_mod_sub_three) c_num2bits) c_less_than) [("n", 10);("k", 50)]big_sub_mod_p *)
