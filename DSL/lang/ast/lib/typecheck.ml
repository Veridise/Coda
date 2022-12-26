open Ast
open Dsl
open Utils

(* circuit declarations *)
type delta = (string * ctyp) list [@@deriving show]
(* typing environment *)
type gamma = (string * typ) list [@@deriving show]

type alpha = qual list [@@deriving show]

let d_empty = []

let g_empty = []

let a_empty = []

let add_to_delta (d: delta) (c: circuit) : delta =
  match c with
  | Circuit {name; signals; property; body} -> (name, (signals,property)) :: d

type cons = 
  | Subtype of gamma * alpha * typ * typ
    [@printer fun fmt (g,a,t1,t2) -> fprintf fmt "Gamma:\n%s\nAlpha:\n%s\n---Subtype---\n%s <: %s" (show_gamma g) (show_alpha a) (show_typ t1) (show_typ t2)]
  | HasType of gamma * alpha * string * typ
    [@printer fun fmt (g,a,x,t) -> fprintf fmt "Gamma:\n%s\nAlpha:\n%s\n---Type---\n%s : %s" (show_gamma g) (show_alpha a) x (show_typ t)]
  | CheckCons of gamma * alpha * qual 
    [@printer fun fmt (g,a,q) -> fprintf fmt "Gamma:\n%s\nAlpha:\n%s\n---Constrain---\n%s" (show_gamma g) (show_alpha a) (show_qual q)]
  [@@deriving show]

let show_cons_list (cs: cons list) : string =
  cs |> List.map show_cons |> String.concat "\n\n"

let map_opt (f: 'a -> 'b option) (xs: 'a list) : 'b list = 
  List.map f xs 
  |> List.filter (function Some _ -> true | _ -> false) 
  |> List.map (function Some y -> y | _ -> failwith "impossible")

let coerce_psingle: typ -> typ = function 
  | TProd ([t], None) -> t
  | t -> t

let functionalize ((signals, q_opt): ctyp) : typ =
  let get_typ (_,t) = t in
  let get_name (x,_) = x in
  let inputs = map_opt (function (x,Input,t) -> Some (x,t) | _ -> None) signals in
  let outputs = map_opt (function (x,Output,t) -> Some (x,t) | _ -> None) signals in 
  let (names_out, ts_out) = List.split outputs in
  let (names_in, ts_in) = List.split inputs in
  let q_opt' = Option.map (fun q -> (names_out, q (List.map v names_in))) q_opt in
  List.fold_right (uncurry tfun) inputs (coerce_psingle (tprod ts_out q_opt'))

let functionalize_circ (Circuit {name; signals; property; body}) : typ =
  functionalize (signals, property)

let rec subtype (g: gamma) (a: alpha) (t1: typ) (t2: typ) : cons list =
  match (t1, t2) with
  | (TRef _, TRef _) -> [Subtype (g, a, t1, t2)]
  | (TFun (x1,s1,t1'), TFun (x2,s2,t2')) ->
    if x1 = x2 then
      Subtype (g, a, s2, s1) :: subtype ((x1,s2)::g) a t1' t2'
    else
      failwith "TODO: subst for function subtyping"
  | (TProd _, TProd _) -> failwith "TODO: product subtyping"
  | (TArr _, TArr _) -> failwith "TODO: array subtyping"
  | _ -> failwith ("Subtype: illegal subtype " ^ (show_typ t1) ^ (show_typ t2))

let rec typecheck (d: delta) (g: gamma) (a: alpha) (e: expr) : (typ * cons list) = 
  let rec f (e: expr) : typ * cons list =
    let (t, cs) = f' e in (coerce_psingle t, cs)
  and f' (e: expr) : typ * cons list = 
    match e with
    | Const c -> 
      let r = fun tb -> TRef (tb, QExpr (eq nu e)) in
      let t = match c with
        | CF _ -> r TF
        | CInt _ -> r TInt
        | CBool _ -> r TBool
        | _ -> failwith "invalid constant"
      in (t, [])
    | Var v ->
      let t = match List.assoc_opt v g with
        | Some t -> t
        | None -> failwith ("No such variable: " ^ v) in
      (t, [])
    | Binop (op, e1, e2) ->
      (* TODO: reflect *)
      let (TRef (tb1, q1), cs1) = f e1 in
      let (TRef (tb2, q2), cs2) = f e2 in
      (match (tb1, tb2) with
      | (TF, TF) | (TInt, TInt) -> (re tb1 (eq nu e), cs1 @ cs2)
      | _ -> failwith ("Binop: Invalid operand type " ^ (show_tyBase tb1) ^ (show_tyBase tb2)))
    | Boolop (op, e1, e2) ->
      (* TODO: reflect *)
      let (TRef (tb1, q1), cs1) = f e1 in
      let (TRef (tb2, q2), cs2) = f e2 in
      (match (tb1, tb2) with
      | (TBool, TBool) -> (re tb1 (eq nu e), cs1 @ cs2)
      | _ -> failwith ("Boolop: Invalid operand type " ^ (show_tyBase tb1) ^ (show_tyBase tb2)))
    | Comp (op, e1, e2) ->
      (* TODO: reflect *)
      (* TODO: rule out invalid cases *)
      let (TRef (tb1, q1), cs1) = f e1 in
      let (TRef (tb2, q2), cs2) = f e2 in
      let res = (TRef (tb1, QExpr (eq nu e)), cs1 @ cs2) in
      (match op with
      | Leq | Lt ->
        (match (tb1, tb2) with 
        | (TInt, TInt) -> res
        | _ -> failwith ("Comp: Cannot compare non-integers for inequality"))
      | _ -> 
        if tb1 = tb2 then res
        else failwith ("Comp: Unequal types " ^ (show_tyBase tb1) ^ (show_tyBase tb1)))
    | Opp e' ->
      let (TRef (tb, q), cs) = f e' in
      (match tb with
      | TF | TInt -> (TRef (tb, QExpr (eq nu e)), cs)
      | _ -> failwith ("Opp: Invalid operand type " ^ (show_tyBase tb)))
    | Not e' ->
      let (TRef (tb, q), cs) = f e' in
      (match tb with
      | TBool -> (TRef (tb, QExpr (eq nu e)), cs)
      | _ -> failwith ("Opp: Invalid operand type " ^ (show_tyBase tb)))
    | Call (circ, args) ->
      (match List.assoc_opt circ d with
      | Some ct -> 
        let (t_args, cs_args) = List.map f args |> List.split  in
        let (t_out, cs_out) = check_app g a (functionalize ct) t_args in
        (t_out, List.concat cs_args @ cs_out)
      | None -> failwith ("No such circuit: " ^ circ))
    | Iter {s; e; body; init; inv} ->
      let (ts, cs) = f s in
      let (te, ce) = f e in
      let (tb, cb) = f body in
      let (tx, cx) = f init in
      let tx_base = match tx with | TRef (t, _) -> t | _ -> failwith "invalid base type" in
      (* s is int *)
      let t_iter = 
        (* TODO: ensure var freshness *)
        tfun "s" tint (
        tfun "e" (TRef (TInt, QExpr (leq (v "s") nu))) (
        tfun "body" (
          (* assume s <= i <= e *)
          tfun "i" (z_range (v "s") (v "e")) (
          (* assume inv(i,x) holds *)
          tfun "x" (TRef (tx_base, inv (v "i") nu))
          (* prove inv(i+1,output) holds *)
          (TRef (tx_base, inv (add z1 (v "i")) nu)))) (
        (* prove inv(s,init) holds *)
        tfun "init" (TRef (tx_base, inv (v "s") nu))
        (* conclude inv(e,output) holds *)
        (TRef (tx_base, inv e nu))))) in 
      check_app g a t_iter [ts; te; tb; tx]
    | Lam (x, t, body) ->
      let (t_body, cs) = typecheck d ((x,t)::g) a body in
      (tfun x t t_body, cs)
    | PCons (es, q_opt) ->
      let (ts, cs_s) = List.map f es |> List.split in
      let cs_q = Option.(q_opt |> map (fun (_, q) -> CheckCons (g, a, q es)) |> to_list) in
      (tprod ts q_opt, List.concat cs_s @ cs_q)
    | PDestr (e1, xs, e2) ->
      let (t1, cs1) = f e1 in
      (match t1 with
      | TProd (ts, q_opt) ->
        let a' = Option.(q_opt |> map (fun (xs, q) -> q (List.map v xs)) |> to_list) in
        let (t2, cs2) = typecheck d (List.combine xs ts) (a' @ a) e2 in
        (t2, cs1 @ cs2)
      | _ -> failwith "not a product")
    | _ -> todo ()
  in f e

and check_app (g: gamma) (a: alpha) (t_f: typ) (t_args: typ list) : typ * cons list =
  (* print_endline ("Function: " ^ show_typ t_f); *)
  (* print_endline (String.concat "\n" (List.map show_typ t_args)); *)
  match t_args with
  | [] -> (t_f, [])
  | t_arg::t_args' ->
    (match t_f with
    | TFun (x, t_x, t_body) ->
      let (t, cs) = check_app ((x,t_arg)::g) a t_body t_args' in
      (t, subtype g a t_arg t_x @ cs)
    | _ -> failwith "Not a function")

let typecheck_stmt (d: delta) (g: gamma) (a: alpha) (s: stmt) : (gamma * alpha * cons list) =
  match s with
  | SSkip -> (g, [], [])
  | SLet(x, t, e) ->
    (* TODO: assert t' :< t *)
    let (t', cs) = typecheck d g a e in
    ((x,t')::g, [], cs)
  | SAssert e ->
    (g, [QExpr e], [])

let rec to_base_typ = function
  | TRef (tb, _) -> TRef (tb, QTrue)
  | TArr (t,_,n) -> TArr (to_base_typ t, QTrue, n)
  | TFun _ -> todos "to_base_typ: TFun"
  | TProd _ -> todos "to_base_typ: TProd"
  [@@deriving show]
  
let init_gamma (c: circuit) : gamma =
  match c with
  | Circuit {name; signals; property; body} ->
    signals |> List.map (function
      (* populate gamma with pre-conditions *)
      | (x,Input,t) -> (x, t) 
      (* ignore post-conditions *)
      | (x,Output,t) -> (x, to_base_typ t)
      (* ignore existential variables *)
      | (x,Exists,t) -> (x, to_base_typ t))

let typecheck_circuit (d: delta) (c: circuit) : cons list =
  match c with
  | Circuit {name; signals; property; body} ->
    let (g, a, cs) = List.fold_left
      (fun ((g, a, cs): gamma * alpha * cons list) (s: stmt) ->
        let (g', a', cs') = typecheck_stmt d g a s in 
        (g', a @ a', cs @ cs'))
      (init_gamma c, [], [])
      body in
    let outputs = List.filter (function (_,Output,_) -> true | _ -> false) signals in
    let out_cons = List.map (fun (x,_,t) -> HasType (g, a, x, t)) outputs in
    let vars_in = signals |> List.filter (function (_,Input,_) -> true | _ -> false) |> List.map (fun (x,_,_) -> x) |> List.map v in
    let vars_out = outputs |> List.map (fun (x,_,_) -> x) |> List.map v in
    let q_cons = property |> Option.map (fun q -> CheckCons (g, a, q vars_in vars_out)) |> Option.to_list in
    cs @ out_cons @ q_cons