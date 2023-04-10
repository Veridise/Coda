open Ast_utils
open Typecheck
open Liblam
module U = Test_utils.Utils

let _ = U.verify ~gamma:[use scale; use pairwise_add] ite_array

(* let t = typ pairwise_add |> show_typ |> print_endline *)
