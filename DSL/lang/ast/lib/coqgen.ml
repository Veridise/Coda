open Ast
open Dsl
open Typecheck
open Utils

let nu_str_coq = "nu"
let spf = Format.sprintf

let tyBase_to_coq (tb: tyBase) : string =
  match tb with
  | TF -> "F"
  | TInt -> "Z"
  | TBool -> "bool"

type ccons = string * string list
let rec typing_to_ccons (e: expr) (t: typ) : ccons =
  match t with
  | TRef (tb, q) -> (tyBase_to_coq tb, [qual_to_coq q])
  | TArr (TRef (tb, q), qa, l) ->
    (spf "(%s) list" (tyBase_to_coq tb),
     [
      (* TODO: handle q (forall) *)
      qual_to_coq (subst_qual nu_str_coq e qa);
      spf "length %s = %s" (expr_to_coq e) (expr_to_coq l)
     ])
  | _ -> todos "xtyp_to_ccons"

and expr_to_coq (e: expr) : string =
  match e with
  | Var x -> if x = "in" then "_in" else x
  | Const c -> 
    (match c with
      | CF n -> spf "%d%%F" n
      (* TODO: sometimes need to force nat *)
      | CInt n -> spf "%d%%Z" n
      | _ -> todos "expr_to_coq: Const")
  | Binop (op, e1, e2) ->
    let op_str = show_binop op in
    spf "(%s %s %s)" (expr_to_coq e1) op_str (expr_to_coq e2)
  | Boolop (op, e1, e2) ->
    let op_str = match op with And -> "/\\" | Or -> "\\/" | Imply -> "->" in
    spf "(%s %s %s)" (expr_to_coq e1) op_str (expr_to_coq e2)
  | Comp (op, e1, e2) ->
    let op_str = show_comp op in
    spf "(%s %s %s)" (expr_to_coq e1) op_str (expr_to_coq e2)
  | Not e ->
    spf "~%s" (expr_to_coq e)
  | Opp e ->
    spf "-%s" (expr_to_coq e)
  | _ -> todos (spf "expr_to_coq: %s" (show_expr e))


and qual_to_coq (q: qual) : string =
  match q with
  | QTrue -> "True"
  | QExpr e -> expr_to_coq e
  | _ -> todos "qual_to_coq"

let gamma_to_coq (g: gamma) : ((string * string) list * string list) =
  List.rev g
  |> List.map (fun (x,t) ->
    let (tb_str, q_strs) = typing_to_ccons (v x) t in
    ((x,tb_str), q_strs))
  |> List.split
  |> fun (b,q) -> (b, List.concat q)

let alpha_to_coq (a: alpha) : string list = 
  List.map qual_to_coq a

let cons_to_coq (c: cons) : string =
  let rename_nu subst = subst nu_str (v nu_str_coq) in
  match c with
  | Subtype (g, a, t1, t2) ->
    let (g_decl, g_ref) = gamma_to_coq g in
    (match t1, t2 with
    | TRef (tb1, q1), TRef (tb2, q2) ->
      (* may assume tb1 = tb2 *)
      if tb1 = tb2 then
        spf "forall %s, %s"
          (String.concat " "
            (List.map
              (fun (x,t) -> spf "(%s : %s)" x t)
              ((nu_str_coq, tyBase_to_coq tb1) :: g_decl)))
          (String.concat " -> "
            (g_ref @ 
            (alpha_to_coq a) @
            [qual_to_coq (rename_nu subst_qual q1);
             qual_to_coq (rename_nu subst_qual q2)]))
      else
        failwith "cons_to_coq: not a refinement")
    | HasType (g, a, x, t) ->
      let (g_decl, g_ref) = gamma_to_coq g in
      let (_, qs) = typing_to_ccons (v x) (rename_nu subst_typ t) in
      spf "forall %s, %s"
        (String.concat " "
          (List.map (fun (x,t) -> spf "(%s : %s)" x t) g_decl))
        (String.concat " -> "
          (g_ref @ 
          (alpha_to_coq a) @
          qs))
let to_numbered (l: 'a list) : (int * 'a) list =
  List.init (List.length l) (fun i -> (i, List.nth l i))

let generate_lemmas (cs: cons list) : string =
  cs |> to_numbered |> List.map (fun (i,c) -> 
    spf "Lemma _obligation%d: %s.\nProof. Admitted." i (cons_to_coq c)) |> String.concat "\n\n"