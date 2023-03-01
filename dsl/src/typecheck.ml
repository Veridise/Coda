open Ast
open Ast_utils
open Dsl
open Utils

(* circuit declarations *)
type delta = (string * circuit) list

(* typing environment *)
type gamma = (string * typ) list
let show_gamma _ = "TODO: show_gamma"

(* assertion store *)
type alpha = qual list
let show_alpha _ = "TODO: show_alpha"

let d_empty = []

let g_empty = []

let a_empty = []

let add_to_delta (d: delta) (c: circuit) : delta =
  match c with
  | Circuit {name; inputs; outputs; dep; body} -> (name, c) :: d

let add_to_deltas (d: delta) (c: circuit list) =
  List.fold_left add_to_delta d c

type cons = 
  | Subtype of gamma * alpha * typ * typ
    [@printer fun fmt (g,a,t1,t2) -> fprintf fmt "Gamma:\n%s\nAlpha:\n%s\n---Subtype---\n%s <: %s" (show_gamma g) (show_alpha a) (show_typ t1) (show_typ t2)]
  | HasType of gamma * alpha * string * typ
    [@printer fun fmt (g,a,x,t) -> fprintf fmt "Gamma:\n%s\nAlpha:\n%s\n---Type---\n%s : %s" (show_gamma g) (show_alpha a) x (show_typ t)]
  | CheckCons of gamma * alpha * qual 
    [@printer fun fmt (g,a,q) -> fprintf fmt "Gamma:\n%s\nAlpha:\n%s\n---Constrain---\n%s" (show_gamma g) (show_alpha a) (show_qual q)]
  [@@deriving show]


let filter_trivial =
  List.filter (function
    | Subtype (_, _, TRef (t1, _), TRef (t2, QTrue)) -> t1 <> t2
    | Subtype (_, _, TRef (t1, QAnd (q1, _)), TRef (t2, q2)) -> q1 <> q2
    | Subtype (_, _, TRef (t1, QAnd (_, q1)), TRef (t2, q2)) -> q1 <> q2
    (* | Subtype (_, _, t1, t2) -> t1 <> t2 *)
    | _ -> true)

let pc (cs: cons list) : unit =
  cs 
  |> filter_trivial 
  |> List.map show_cons |> String.concat "\n\n" |> print_endline

let functionalize_circ (Circuit {name; inputs; outputs; dep; body}) : typ =
  let get_typ = snd in
  let get_name = fst in
  let out_types = outputs |> List.map get_typ in
  let out_type = match dep with
    | None -> ttuple out_types
    | Some q -> tdprod out_types (List.map get_name outputs) q in
  List.fold_right (uncurry tfun) inputs out_type

let rec subtype (g: gamma) (a: alpha) (t1: typ) (t2: typ) : cons list =
  match (t1, t2) with
  | (TRef (tb1, _), TRef (tb2, _)) ->
    if tb1 = tb2 then [Subtype (g, a, t1, t2)]
    else failwith (Format.sprintf "Subtype: different base types for %s and %s" (show_typ t1) (show_typ t2))
  | (TFun (x,t1,t2), TFun (y,t1',t2')) ->
    Subtype (g, a, t1', t1) :: subtype ((x,t1')::g) a t2 (subst_typ y (v x) t2')
  | (TTuple ts1, TTuple ts2) -> List.concat_map (uncurry (subtype g a)) (List.combine ts1 ts2)
  | (TDProd (ts1, xs, q1), TDProd (ts2, ys, q2)) ->
    let q1' = List.fold_right (fun (x,y) q -> subst_qual x (v y) q) (List.combine xs ys) q1 in
    List.concat_map (uncurry (subtype g a)) (List.combine ts1 ts2) @
    [CheckCons (g, a, qimply q1' q2)]
      (* failwith (Format.sprintf "TODO: product subtyping %s <: %s" (show_typ t1) (show_typ t2)) *)
  | (TArr _, TArr _) -> failwith "TODO: array subtyping"
  | (TTuple ts1, TDProd (ts2, _, _)) ->
      List.concat_map (uncurry (subtype g a)) (List.combine ts1 ts2)
  (* | (TDProd (ts2, xs, q), TTuple ts1) -> *)
      (* cts = List.concat_map (uncurry (subtype g a)) (List.combine ts1 ts2) in *)


  | _ -> failwith (Format.sprintf "Subtype: illegal subtype: t1=%s t2=%s" (show_typ t1) (show_typ t2))

let coerce_psingle : typ -> typ = function
  | TTuple [t] -> t
  | t -> t

let refine (t: typ) (q: qual) : typ =
  match t with
  | TRef (tb, q') -> TRef (tb, qand q' q)
  | TArr (t, q', el) -> TArr (t, qand q' q, el)
  | TTuple _ -> failwith "Cannot refine TTuple"
  | TFun _ -> failwith "Cannot refine TFun"

let rec synthesize (d: delta) (g: gamma) (a: alpha) (e: expr) : (typ * cons list) = 
  print_endline (Format.sprintf "Synthesizing type for %s" (show_expr e));
  let rec f (e: expr) : typ * cons list =
    let (t, cs) = f' e in (coerce_psingle t, cs)
  and f' (e: expr) : typ * cons list = 
    match e with
    | NonDet -> (tfq QTrue, [])
    | CPrime -> (TRef (TInt, QExpr (eq nu CPrime)), [])
    | CPLen -> (TRef (TInt, QExpr (eq nu CPLen)), [])
    | Const c -> 
      let r = fun tb -> TRef (tb, QExpr (eq nu e)) in
      let t = match c with
        | CF _ -> r TF
        | CInt _ -> r TInt
        | CBool _ -> r TBool
        | _ -> failwith (Format.sprintf "synthesize: invalid constant %s" (show_expr e))
      in (t, [])
    | Var v ->
      let t = match List.assoc_opt v g with
        | Some t -> t
        | None -> failwith ("No such variable: " ^ v) in
      (t, [])
    | Ascribe (e, t) ->
      let cs = check d g a e t in (t, cs)
    | AscribeUnsafe (x, t) -> (t, [])
    | LamA (x, t1, e) ->
      let (t2, cs) = synthesize d ((x,t1)::g) a e in
      (tfun x t1 t2, cs)
    | App (e1, e2) ->
      let (t1, cs1) = f e1 in
      (match t1 with
      | TFun (x, tx, tr) ->
        let cs2 = check d g a e2 tx in
        (subst_typ x e2 tr, cs1 @ cs2)
      | _ -> failwith (Format.sprintf "App: not a function: %s" (show_typ t1)))
    | Binop (BF, op, e1, e2) ->
      let cs1 = check d g a e1 tf in 
      let cs2 = check d g a e1 tf in 
      (tfe (eq nu e), cs1 @ cs2)
    | Binop (_, op, e1, e2) ->
      let cs1 = check d g a e1 tint in 
      let cs2 = check d g a e1 tint in 
      (re TInt (eq nu e), cs1 @ cs2)
    | Boolop (op, e1, e2) ->
      (* TODO: reflect *)
      let (TRef (tb1, q1), cs1) = f e1 in
      let (TRef (tb2, q2), cs2) = f e2 in
      (match (tb1, tb2) with
      | (TBool, TBool) -> (re tb1 (eq nu e), cs1 @ cs2)
      | _ -> failwith (Format.sprintf "Boolop: Invalid operand type %s and %s" (show_tyBase tb1) (show_tyBase tb2)))
    | Comp (op, e1, e2) ->
      (* TODO: reflect *)
      (* TODO: rule out invalid cases *)
      let (TRef (tb1, q1), cs1) = f e1 in
      let (TRef (tb2, q2), cs2) = f e2 in
      let res = (TRef (TBool, QExpr (eq nu e)), cs1 @ cs2) in
      (match op with
      | Leq | Lt ->
        (match (tb1, tb2) with 
        | (TInt, TInt) -> res
        | _ -> failwith ("Comp: Cannot compare non-integers for inequality"))
      | _ -> 
        if tb1 = tb2 then res
        else failwith ("Comp: Unequal types " ^ (show_tyBase tb1) ^ (show_tyBase tb1)))
    | Not e' ->
      let (TRef (tb, q), cs) = f e' in
      (match tb with
      | TBool -> (TRef (tb, QExpr (eq nu e)), cs)
      | _ -> failwith ("Opp: Invalid operand type " ^ (show_tyBase tb)))
    | Call (c_name, args) ->
      (match List.assoc_opt c_name d with
      | Some c ->
          let ctype = functionalize_circ c in
          synthesize d g a (dummy_apps c_name ctype args)
      | None -> failwith ("No such circuit: " ^ c_name))
    | Sum {s=s; e=e'; body=b} ->
      let cs1 = check d g a s tint in
      let cs2 = check d g a e' tint in
      let b' = match b with
        | Lam (x, b') -> LamA (x, z_range s e', b')
        | _ -> failwith "Sum's body must be Lam" in
      let (t_body, cs3) = f b' in
      (match t_body with
      | TFun (i, TRef (TInt, _), TRef (tb', _)) ->
        (match tb' with
        | TInt | TF ->
          (TRef (tb', QExpr (eq nu (rsum s e' t_body))), cs1 @ cs2 @ cs3)
        | _ -> failwith (Format.sprintf "Sum: %s is not summable" (show_tyBase tb')))
      | _ -> failwith (Format.sprintf "Sum: body has type %s" (show_typ t_body)))
    | Iter {s; e; body; init; inv} ->
      let (tx, cx) = f init in
      (* s is int *)
      let t_iter = 
        (* TODO: ensure var freshness *)
        tfun "s" tint
        (tfun "e" tint
        (tfun "body" (
          (* assume s <= i < e *)
          (tfun "i" (z_range_co s e)
          (* assume inv(i,x) holds *)
          (tfun "x" (inv (v "i") nu)
          (* prove inv(i+1,output) holds *)
          (inv (nadd z1 (v "i")) nu))))
        (* prove inv(s,init) holds *)
        (tfun "init" (inv (v "s") nu)
        (* conclude inv(e,output) holds *)
        (inv (v "e") nu)))) in 
      synthesize d g a (dummy_apps "iter" t_iter [s;e;body;init])
      (* synthesize_app d g a t_iter [s; e; body; init] *)
    | TMake es ->
      let (ts, cs_s) = List.(map f es |> split) in
      (ttuple ts, List.concat cs_s)
    | TGet (e, n) ->
      let (t, cs) = f e in
      (match t with
      | TTuple ts | TDProd (ts, _, _) -> 
        if 0 <= n && n < List.length ts then
          (List.nth ts n, cs)
        else
          failwith "Tuple access out of bounds"
      | _ -> failwith "Synthesize: expect tuple type")
    | ArrayOp (Get, [e1; e2]) ->
      let (t1, cs1) = f e1 in
      (match t1 with
      | TArr (t, q, el) ->
        (* check index in range *)
        let cs2 = check d g a e2 (z_range z0 (nsub1 el)) in
        (refine t (QExpr (eq nu e)), cs1 @ cs2)
      | _ -> failwith "Synthesize: get: not an array")
    | ArrayOp (Cons, [e1; e2]) ->
      let (t2, cs2) = f e2 in
      (match t2 with
      | TArr (t, q, el) ->
        let cs1 = check d g a e1 t in
        (TArr (t, QExpr (eq nu e), nadd1 el), cs1 @ cs2)
      | _ -> failwith "Synthesize: cons: not an array")
    | ArrayOp (Take, [e1; e2]) ->
      let (t1, cs1) = f e1 in
      (match t1 with
      | TArr (t, q, el) ->
        (* check index in range *)
        let cs2 = check d g a e2 (z_range z0 el) in
        (TArr (t, QExpr (eq nu e), e2), cs1 @ cs2)
      | _ -> failwith "Synthesize: take: not an array")
    | ArrayOp (Drop, [e1; e2]) ->
      let (t1, cs1) = f e1 in
      (match t1 with
      | TArr (t, q, el) ->
        (* check index in range *)
        let cs2 = check d g a e2 (z_range z0 el) in
        (TArr (t, QExpr (eq nu e), zsub el e2), cs1 @ cs2)
      | _ -> failwith "Synthesize: drop: not an array")
    | ArrayOp (Zip, [e1; e2]) ->
      let (t1, cs1) = f e1 in
      let (t2, cs2) = f e2 in
      (match (t1, t2) with
      | TArr (t1', q1, l1), TArr (t2', q2, l2) ->
        (* FIXME: q1 and q2 are erased *)
        (tarr (ttuple [t1';t2']) QTrue l1, cs1 @ cs2 @ [CheckCons (g, a, (QExpr (eq l1 l2)))])
      | TArr _, _ | _, TArr _ -> failwith "zip: not an array")
    | ArrayOp (op, _) ->
      failwith (Format.sprintf "synthesize: ArrayOp: %s not implemented" (show_aop op))
    | Map (e1, e2) ->
      let (t1, cs1) = f e1 in
      let (t2, cs2) = f e2 in
      (match t1, t2 with
      | TFun (x,tx, TRef (tr,q)), TArr (t2', q2, el) ->
        (* todo: factor out non-dependent part of q *)
        (* FIXME: q is erased *)
        let i = "i" in
        let q2' = q |> subst_qual x (get e2 (v i)) |> subst_qual nu_str (get nu (v i)) in
        (TArr (
          TRef (tr, QTrue),
          qand (qforall i z0 el q2') (QExpr (eq nu (Map (e1,e2)))),
          el),
        cs1 @ cs2 @ subtype g a t2' tx)
      | _, TArr _ -> failwith "map: not a valid function"
      | TFun _, _ -> failwith "map: not a valid array")
    | DPCons (es, xs, q) ->
      let (ts, css) = List.map f es |> List.split in
      (* TODO: this might be too weak and we need to substitute *)
      let g' = List.combine xs ts in
      let t = tdprod ts xs q in
      (t, List.concat css @ [CheckCons (g' @ g, a, q)])
    (* | DPDestr (e1, xs, e2) -> *)
    | _ -> failwith (Format.sprintf "Synthesis unavailable for expression %s" (show_expr e))
  in 
  let (t, cs) = f e in
  print_endline (Format.sprintf "Synthesized type for %s: %s" (show_expr e) (show_typ t));
  (t, cs)

and synthesize_app (d: delta) (g: gamma) (a: alpha) (t: typ) (es: expr list) : typ * cons list =
  match es with
  | [] -> (t, [])
  | e::es' ->
    (match t with
    | TFun (x, t1, t2) ->
      let (t, cs) = synthesize_app d ((x,t1)::g) a t2 es' in
      (t, check d g a e t1 @ cs)
    | _ -> failwith "Not a function")

and check (d: delta) (g: gamma) (a: alpha) (e: expr) (t: typ) : cons list =
  print_endline (Format.sprintf "Checking %s has type %s" (show_expr e) (show_typ t));
  match (e, t) with
  | (Const CNil, TArr (t1, QTrue, e)) -> [CheckCons (g, a, QExpr (eq e z0))]
  | (Lam (x, body), TFun (y, t1, t2)) ->
      check d ((x,t1)::g) a body t2
  | (LamA (x, t, body), TFun (y, t1, t2)) -> 
      subtype g a t1 t @ check d ((x,t1)::g) a body t2
  | (LetIn (x, e1, e2), t2) ->
    let (t1, cs) = synthesize d g a e1 in
    check d ((x,t1)::g) a e2 t2
  | (DPDestr (e1, xs, e2), t2) ->
    let (t1, cs1) = synthesize d g a e1 in
    let (ts, a') =
      match t1 with
      | TDProd (ts, ys, q) ->
        let q' = List.fold_right (fun (x,y) q -> subst_qual x (v y) q)
          (List.combine xs ys) q in
        print_endline (Format.sprintf "check: DPDestr: subst'ed q: %s" (show_qual q'));
        (ts, [q'])
      | TTuple ts ->
        (ts, [])
      | _ -> failwith "not a product"
    in if List.length ts = List.length xs then
      let cs2 = check d (List.combine xs ts) (a @ a') e2 t2 in
      cs1 @ cs2
    else
      failwith (Format.sprintf "DPDestr: xs and ts have different lengths")
  | _ ->
    let (t', cs) = synthesize d g a e in
    cs @ subtype g a t' t

  (* (tfun x t t_body, cs) *)

let typecheck_stmt (d: delta) (g: gamma) (a: alpha) (s: stmt) : (gamma * alpha * cons list) =
  match s with
  | SSkip -> (g, [], [])
  | SLet(x, e) ->
    let (t', cs) = synthesize d g a e in
    ((x,t')::g, [], cs)
  | SAssert (e1, e2) ->
    (* TODO: check q is well-formed and has restricted form *)
    (g, [qeq e1 e2], [])
  | _ -> todos "typcheck_stmt"

let rec to_base_typ = function
  | TRef (tb, _) -> TRef (tb, QTrue)
  | TArr (t,_,n) -> TArr (to_base_typ t, QTrue, n)
  | TFun _ -> todos "to_base_typ: TFun"
  | TTuple _ -> todos "to_base_typ: TTuple"
  | TDProd _ -> todos "to_base_typ: TDProd"
  
let init_gamma (c: circuit) : gamma =
  let to_base_types = List.map (fun (x,t) -> (x, to_base_typ t)) in
  match c with
  | Circuit {name; inputs; outputs; dep; body} ->
     List.rev (to_base_types outputs) @ List.rev inputs

let typecheck_circuit (d: delta) (c: circuit) : cons list =
  match c with
  | Circuit {name; inputs; outputs; dep; body} ->
    let (g, a, cs) = List.fold_left
      (fun ((g, a, cs): gamma * alpha * cons list) (s: stmt) ->
        let (g', a', cs') = typecheck_stmt d g a s in 
        (g', a @ a', cs @ cs'))
      (init_gamma c, [], [])
      body in
    let out_cons = List.map (fun (x,t) -> HasType (g, a, x, t)) outputs in
    let dep_cons = dep |> Option.map (fun q -> CheckCons (g, a, q)) |> Option.to_list in
    (* let vars_in = inputs |> List.map (fun (x,_) -> x) |> List.map v in *)
    (* let vars_out = outputs |> List.map (fun (x,_) -> x) |> List.map v in *)
    cs @ out_cons @ dep_cons