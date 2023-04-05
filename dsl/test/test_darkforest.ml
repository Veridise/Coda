open Core
open Typecheck
open Coqgen
open Darkforest
module U = Test_utils.Utils

let _ = U.test calc_total []

let _ =
  U.test quin_selector
    (Circomlib.(Comparators.[is_equal; less_than]) @ [calc_total])
