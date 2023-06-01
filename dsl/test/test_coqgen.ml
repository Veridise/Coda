open Ast
open Ast_utils
open Coqgen
open Dsl
open Core

(* array *)
let t =
  refine_expr
    (tarr (refine_expr (refine_expr tf (eq nu f0)) (eq nu f1)))
    (eq nu f2)

let {coq_typ; ref} = typ_to_coq t ;;

print_endline (spf "coq_typ: %s" coq_typ) ;;

List.iter ref ~f:(fun r -> print_endline (spf "ref: %s" (r "x")))

(* tuple *)
let t =
  refine_expr
    (ttuple [refine_expr tf (eq nu f0); refine_expr tf (eq nu f1)])
    (eq (tget nu 0) (tget nu 1))

let {coq_typ; ref} = typ_to_coq t ;;

print_endline (spf "coq_typ: %s" coq_typ) ;;

List.iter ref ~f:(fun r -> print_endline (spf "ref: %s" (r "x")))

open Notation

let gamma =
  [ ("f", tfun "x" tf (refine tf (nu ==. v "x" +% f1)))
  ; ("xs", tarr_t_k tf (zn 10))
  ; ("ys", tarr_t_k tint (zn 11)) ]

let e = Map (v "f", v "xs")

let t, _ = Typecheck.(S.run {cs= []; gamma; alpha= []; delta= []} (synthesize e))

let e' = ArrayOp (Zip, [v "xs"; v "ys"])

let t', _ =
  Typecheck.(S.run {cs= []; gamma; alpha= []; delta= []} (synthesize e'))
;;

print_endline (spf "map: %s" (show_typ t)) ;;

print_endline (spf "zip: %s" (show_typ t'))
