open Ast_utils
open Typecheck
open Liblam
module U = Test_utils.Utils

let _ = verify ~gamma:[] gen_rng
let t = typ gen_rng |> show_typ |> print_endline;;