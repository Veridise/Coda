open Core
open Ast
open Ast_utils
open Dsl
open Notation

let t =
  refine_expr (refine_expr (tarr (refine_expr (refine_expr tf f0) f1)) z0) z1

let t' = normalize t ;;

print_endline (show_typ t) ;;

print_endline (show_typ t')
