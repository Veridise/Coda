open Core
open Typecheck
open Coqgen
open Semaphore
module U = Test_utils.Utils

let _ = U.test calc_secret Circomlib.Poseidon.[poseidon]

let _ = U.test calc_id_commit Circomlib.Poseidon.[poseidon]

let _ = U.test calc_null_hash Circomlib.Poseidon.[poseidon]

let _ =
  U.test mrkl_tree_incl_pf Circomlib.(Poseidon.[poseidon] @ Mux1.[multi_mux_1])

let _ =
  U.test semaphore
    [calc_secret; calc_id_commit; calc_null_hash; mrkl_tree_incl_pf]

