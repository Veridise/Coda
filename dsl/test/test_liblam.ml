open Ast_utils
open Typecheck
open Liblam
module U = Test_utils.Utils

let _ = verify ~gamma:[] scale

(* let t = typ pairwise_add |> show_typ |> print_endline *)
