open Core
open Typecheck
open Coqgen
open Bigint
open Big_sub
module U = Test_utils.Utils

(* let _ = U.test mod_sub_three [Circomlib.Comparators.less_than] *)
let _ = U.test big_sub [mod_sub_three]
