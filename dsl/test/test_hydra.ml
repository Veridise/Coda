open Core
open Typecheck
open Coqgen
open Hydra
module U = Test_utils.Utils

let _ = U.test position_switcher []

let _ =
  U.test vrfy_mrkl_path Circomlib.(Poseidon.[poseidon] @ [position_switcher])
