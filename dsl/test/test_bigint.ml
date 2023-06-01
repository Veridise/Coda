open Core
open Typecheck
open Coqgen
open Circomlib
open Bigint
module U = Test_utils.Utils

let _ = U.test Big_is_zero.c_big_is_zero Circomlib.Comparators.[is_zero]

let _ =
  U.test Big_is_equal.c_big_is_equal Circomlib.(Comparators.[is_zero; is_equal])

let _ = U.test Big_add.mod_sum_three Circomlib.Bitify.[num2bits]

let _ =
  U.test Big_add.big_add (Circomlib.Bitify.[num2bits] @ Big_add.[mod_sum_three])

let _ =
  U.test Big_add.big_add_mod_p
    ( Circomlib.Bitify.[num2bits]
    @ Big_add.[big_add; mod_sum_three]
    @ Big_sub.[big_sub]
    @ Big_less_than.[big_lt] )

let _ = U.test Split.split Circomlib.Bitify.[num2bits]

let _ = U.test Split.split_three Circomlib.Bitify.[num2bits]

let _ =
  U.test Big_less_than.big_lt
    Circomlib.(
      Comparators.[less_than; is_equal] @ Gates.[cand; cor] @ Bitify.[num2bits] )

let _ =
  U.test Big_sub.mod_sub_three
    Circomlib.(Bitify.[num2bits] @ Comparators.[less_than])

let _ =
  U.test Big_sub.big_sub
    Circomlib.(
      Bitify.[num2bits] @ Comparators.[less_than] @ Big_sub.[mod_sub_three] )

let _ =
  U.test Big_sub.big_sub_mod_p
    Circomlib.(
      Bitify.[num2bits]
      @ Comparators.[less_than]
      @ Big_sub.[mod_sub_three; big_sub]
      @ Big_add.[big_add] )
