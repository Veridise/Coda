open Ast
open Ast_utils
open Dsl
open Typecheck
open Utils

let nu_str_coq = "nu"

let spf = Format.sprintf

let counter = ref 0
(* let inc () = (let i = !counter; counter := i + 1; i)
   let fresh x = x ^ inc () *)

let base_to_coq (tb : base) : string =
  match tb with TF -> "F" | TInt -> "Z" | TBool -> "bool"

let get_base (t : typ) : base =
  match skeleton t with
  | TBase tb ->
      tb
  | _ ->
      failwith (spf "get_base: %s" (show_typ t))

type ccons = string * string list

let rec typing_to_ccons (e : expr) (t : typ) : ccons =
  let is_nat = QExpr (leq z0 nu) in
  print_endline (spf "typing to ccons: %s :: %s" (show_expr e) (show_typ t)) ;
  match t with
  | TRef (TInt, q) when q = is_nat ->
      ("nat", [])
  | TRef (TInt, QAnd (q1, q2)) when q1 = is_nat ->
      ("nat", [qual_to_coq (subst_qual nu_str e q2)])
  | TRef (tb, q) ->
      (base_to_coq tb, [qual_to_coq (subst_qual nu_str e q)])
  | TArr (TRef (tb, q), qa, l) ->
      (* TODO: support nested arrays *)
      let x = fresh "x" in
      ( spf "list %s" (base_to_coq tb)
      , [ (* TODO: handle q (forall) *)
          spf "Forall (fun %s => %s) %s" x
            (qual_to_coq (subst_qual nu_str (v x) q))
            (expr_to_coq e)
        ; qual_to_coq (subst_qual nu_str e qa)
        ; spf "length %s = %s" (expr_to_coq e) (expr_to_coq l) ] )
  | TTuple ts ->
      let tbs = ts |> List.map get_base |> List.map base_to_coq in
      (spf "%s" (String.concat " * " tbs), [])
  | TDProd (ts, xs, q) ->
      let tb_str =
        if List.length ts = 0 then "unit"
        else
          ts |> List.map get_base |> List.map base_to_coq
          |> fun ss -> spf "%s" (String.concat " * " ss)
      in
      let xs_str = if List.length ts = 0 then "_" else String.concat "," xs in
      let qstr =
        spf "match %s with (%s) => %s end" (expr_to_coq e) xs_str
          (qual_to_coq q)
      in
      (tb_str, [qstr])
  | TFun _ ->
      todos "xtyp_to_ccons: TFun"

and expr_to_coq (e : expr) : string =
  match e with
  | Var x ->
      if x = "in" then "_in" else x
  | Const c -> (
    match c with
    | CF n ->
        spf "%d%%F" n
    (* TODO: sometimes need to force nat *)
    | CInt n ->
        if n >= 0 then spf "%d%%nat" n else spf "%d%%Z" n
    | _ ->
        todos "expr_to_coq: Const" )
  | CPrime ->
      "C.q"
  | CPLen ->
      "C.k"
  | Binop (t, op, e1, e2) ->
      let trailer = match t with BF -> "F" | BZ -> "Z" | BNat -> "nat" in
      let op_str = show_binop op in
      spf "(%s %s %s)%%%s" (expr_to_coq e1) op_str (expr_to_coq e2) trailer
  | Boolop (op, e1, e2) ->
      let op_str = match op with And -> "/\\" | Or -> "\\/" | Imply -> "->" in
      spf "(%s %s %s)" (expr_to_coq e1) op_str (expr_to_coq e2)
  | Comp (op, e1, e2) ->
      let op_str = show_comp op in
      spf "(%s %s %s)" (expr_to_coq e1) op_str (expr_to_coq e2)
  | Not e ->
      spf "~%s" (expr_to_coq e)
  | Fn (Unint f, es) ->
      let f' =
        match f with
        | "and" ->
            "f_and"
        | "or" ->
            "f_or"
        | "not" ->
            "f_not"
        | "nand" ->
            "f_nand"
        | "nor" ->
            "f_nor"
        | "xor" ->
            "f_xor"
        | _ ->
            f
      in
      spf "(%s %s)" f' (String.concat " " (List.map expr_to_coq es))
  | Fn (ToBigUZ, [n; xs]) ->
      spf "[\\ %s \\]" (expr_to_coq xs)
  | Fn (ToUZ, [e]) ->
      spf "F.to_Z %s" (expr_to_coq e)
  | ArrayOp (aop, [e1; e2]) -> (
    match aop with
    | Take ->
        spf "%s[:%s]" (expr_to_coq e1) (expr_to_coq e2)
    | Get ->
        spf "%s!%s" (expr_to_coq e1) (expr_to_coq e2)
    | _ ->
        failwith (spf "expr_to_coq: %s not implemented" (show_aop aop)) )
  | ArrayOp (aop, _) ->
      failwith (spf "expr_to_coq: ArrayOp %s wrong arity" (show_aop aop))
  | TGet (e1, 0) ->
      spf "fst (%s)" (expr_to_coq e1)
  | TGet (e1, 1) ->
      spf "snd (%s)" (expr_to_coq e1)
  | _ ->
      todos (spf "expr_to_coq: %s" (show_expr e))

and qual_to_coq (q : qual) : string =
  match q with
  | QTrue ->
      "True"
  | QExpr e ->
      expr_to_coq e
  | QNot q' ->
      spf "~(%s)" (qual_to_coq q')
  | QAnd (q1, q2) ->
      spf "(%s /\\ %s)" (qual_to_coq q1) (qual_to_coq q2)
  | QImply (q1, q2) ->
      spf "(%s -> %s)" (qual_to_coq q1) (qual_to_coq q2)
  | QForall ((x, s, e), q) ->
      spf "(forall (%s:%s), %s <= %s < %s -> %s)" x "nat" (expr_to_coq s) x
        (expr_to_coq e) (qual_to_coq q)
  | _ ->
      todos "qual_to_coq"

let gamma_to_coq (g : gamma) : (string * string) list * string list =
  List.rev g
  |> List.map (fun (x, t) ->
         let tb_str, q_strs = typing_to_ccons (v x) t in
         ((x, tb_str), q_strs) )
  |> List.split
  |> fun (b, q) -> (b, List.concat q)

(* (b,
   let qs = List.concat q in
   print_endline ("Gamma Q: " ^ (String.concat "/\\" qs));
   qs
   ) *)

let alpha_to_coq (a : alpha) : string list = List.map qual_to_coq a

let cons_to_coq (c : cons) : string =
  let rename_nu subst = subst nu_str (v nu_str_coq) in
  match c with
  | Subtype (g, a, t1, t2) -> (
      let g_decl, g_ref =
        g
        (* debug *)
        (* |> List.filter (fun (x,_) -> x = "x")  *)
        |> gamma_to_coq
      in
      match (t1, t2) with
      | TRef (tb1, q1), TRef (tb2, q2) ->
          (* may assume tb1 = tb2 *)
          if tb1 = tb2 then
            spf "forall %s, %s"
              (String.concat " "
                 (List.map
                    (fun (x, t) -> spf "(%s : %s)" x t)
                    ((nu_str_coq, base_to_coq tb1) :: g_decl) ) )
              (String.concat " -> "
                 ( g_ref @ alpha_to_coq a
                 @ [ qual_to_coq (rename_nu subst_qual q1)
                   ; qual_to_coq (rename_nu subst_qual q2) ] ) )
          else failwith "cons_to_coq: not a refinement" )
  | HasType (g, a, x, t) ->
      let g_decl, g_ref = gamma_to_coq g in
      let _, qs = typing_to_ccons (v x) (subst_typ nu_str (v x) t) in
      spf "forall %s, %s"
        (String.concat " "
           (List.map (fun (x, t) -> spf "(%s : %s)" x t) g_decl) )
        (String.concat " -> " (g_ref @ alpha_to_coq a @ qs))
  | CheckCons (g, a, q) ->
      let g_decl, g_ref = gamma_to_coq g in
      spf "forall %s, %s"
        (String.concat " "
           (List.map (fun (x, t) -> spf "(%s : %s)" x t) g_decl) )
        (String.concat " -> " (g_ref @ alpha_to_coq a @ [qual_to_coq q]))

let generate_lemmas (cs : cons list) : string =
  cs |> to_numbered
  |> List.map (fun (i, c) ->
         spf "Lemma _obligation%d: %s.\nProof. Admitted." i (cons_to_coq c) )
  |> String.concat "\n\n"
