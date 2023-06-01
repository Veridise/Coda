open Core
open Typecheck
open Coqgen
open Hydra
module U = Test_utils.Utils

let _ = U.test position_switcher []

let _ =
  U.test vrfy_mrkl_path Circomlib.(Poseidon.[poseidon] @ [position_switcher])

let _ =
  U.test vrfy_hydra_commit Circomlib.(Poseidon.[poseidon; vrfy_eddsa_poseidon])

let _ =
  U.test hydra_s1
    Circomlib.(
      Comparators.[leq]
      @ Bitify.[num2bits]
      @ Poseidon.[poseidon]
      @ [vrfy_hydra_commit; vrfy_mrkl_path] )
