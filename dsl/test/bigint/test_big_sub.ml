open Core
open Bigint
open Big_add
open Big_sub
module U = Test_utils.Utils

(* let _ = U.test mod_sub_three [Circomlib.Comparators.less_than] *)
let _ = U.test big_sub_mod_p [big_add; big_sub]
