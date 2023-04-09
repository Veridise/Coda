open Core
open Typecheck
open Coqgen
open Circomlib.Mux1
module U = Test_utils.Utils

let _ = U.test multi_mux_1 []
