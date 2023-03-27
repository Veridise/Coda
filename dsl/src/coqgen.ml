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

type typing = {coq_typ: string; ref: (string -> string) list}

let rec typ_to_coq (t : typ) : typing =
  let is_nat = QExpr (leq z0 nu) in
  let t' = normalize t in
  let subst_nu = subst_qual nu_str in
  let lift_qual q x = qual_to_coq (subst_nu (v x) q) in
  let lift_true _ = qual_to_coq QTrue in
  print_endline (spf "[typ_to_coq] %s" (show_typ t)) ;
  print_endline (spf "[typ_to_coq] Normalized: %s" (show_typ t')) ;
  match t' with
  | TRef (TBase TInt, q) when q = is_nat ->
      {coq_typ= "nat"; ref= []}
  | TRef (TBase TInt, QAnd (q1, q2)) when q1 = is_nat ->
      {coq_typ= "nat"; ref= [lift_qual q2]}
  | TRef (TBase tb, q) ->
      {coq_typ= base_to_coq tb; ref= [lift_qual q]}
  | TRef (TArr t_elem, q) ->
      let c = typ_to_coq t_elem in
      (* TODO: support nested arrays *)
      let x = fresh "x" in
      { coq_typ= spf "(list %s)" c.coq_typ
      ; ref=
          List.map (fun r xs -> spf "Forall (fun %s => %s) %s" x (r x) xs) c.ref
          @ [lift_qual q] }
      (* let tbs = ts |> List.map get_base |> List.map base_to_coq in
         (spf "%s" (String.concat " * " tbs), []) *)
  | TRef (TTuple ts, q) ->
      let l = List.length ts in
      let cs = List.map typ_to_coq ts in
      let tup_str =
        if l = 0 then "unit"
        else
          cs
          |> List.map (fun (c : typing) -> c.coq_typ)
          |> fun ss -> spf "%s" (String.concat " * " ss)
      in
      let xs_str = List.init l (fun _ -> fresh "x") in
      let xs_pat = if l = 0 then "_" else String.concat "," xs_str in
      let xs_ref =
        cs
        |> List.mapi (fun i (c : typing) ->
               let x = List.nth xs_str i in
               List.map (fun r -> r x) c.ref )
        |> List.concat
      in
      let ref_match body tup =
        spf "match %s with (%s) => %s end" tup xs_pat body
      in
      let ref_q =
        ref_match
          ( List.fold_right
              (fun (i, xi) -> subst_qual' (tget nu i) (v xi))
              (to_numbered xs_str) q
          |> qual_to_coq )
      in
      let xs_ref_match = List.map (fun xi_ref -> ref_match xi_ref) xs_ref in
      {coq_typ= tup_str; ref= xs_ref_match @ [ref_q]}
  | TFun _ ->
      todos "typ_to_coq: TFun"
  | _ ->
      todos "typ_to_coq: TODO"

and expr_to_coq (e : expr) : string =
  match e with
  | Var x ->
      if x = "in" then "_in" else x
  | Const c -> (
    match c with
    | CF n ->
        spf "%s%%F" (Z.to_string n)
    (* TODO: sometimes need to force nat *)
    | CInt n ->
        if Z.(n >= zero) then spf "%s%%nat" (Z.to_string n)
        else spf "%s%%Z" (Z.to_string n)
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
         let {coq_typ; ref} = typ_to_coq t in
         ((x, coq_typ), List.map (fun r -> r x) ref) )
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
