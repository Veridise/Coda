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
  | HasType of gamma * alpha * string * typ
  | CheckCons of gamma * alpha * qual 
  [@@deriving show]

let map_opt (f: 'a -> 'b option) (xs: 'a list) : 'b list = 
  List.map f xs 
  |> List.filter (function Some _ -> true | _ -> false) 
  |> List.map (function Some y -> y | _ -> failwith "impossible")

let functionalize ((signals, q_opt): ctyp) : typ =
  let get_typ (_,t) = t in
  let get_name (x,_) = x in
  let inputs = map_opt (function (x,Input,t) -> Some (x,t) | _ -> None) signals in
  let outputs = map_opt (function (x,Output,t) -> Some (x,t) | _ -> None) signals in 
  let (xs_out, ts_out) = List.split outputs in
  let q = Option.map (fun q -> (xs_out, q)) q_opt in
  List.fold_right (uncurry tfun) inputs (tprod ts_out q)

let rec typecheck (d: delta) (g: gamma) (a: alpha) (e: expr) : (typ * cons list) = 
  let rec f (e: expr) : typ * cons list = 
    match e with
    | Const c -> 
      let t = match c with
        | CF _ -> TRef (TF, QExpr (eq (v "nu") e))
        | CInt _ -> TRef (TInt, QExpr (eq (v "nu") e))
        | _ -> failwith "invalid constant"
      in (t, [])
    | Var v ->
      let t = match List.assoc_opt v g with
        | Some t -> t
        | None -> failwith ("No such variable: " ^ v) in
      (t, [])
    | Binop (op, e1, e2) ->
      (* TODO: reflect *)
      (* TODO: rule out invalid cases *)
      let (TRef (tb1, q1), cs1) = f e1 in
      let (TRef (tb2, q2), cs2) = f e2 in
      (TRef (tb1, QExpr (eq (v "nu") e)), cs1 @ cs2)
    | Boolop (op, e1, e2) ->
      (* TODO: reflect *)
      (* TODO: rule out invalid cases *)
      let (TRef (tb1, q1), cs1) = f e1 in
      let (TRef (tb2, q2), cs2) = f e2 in
      (TRef (tb1, QExpr (eq (v "nu") e)), cs1 @ cs2)
    | Comp (op, e1, e2) ->
      (* TODO: reflect *)
      (* TODO: rule out invalid cases *)
      let (TRef (tb1, q1), cs1) = f e1 in
      let (TRef (tb2, q2), cs2) = f e2 in
      (TRef (tb1, QExpr (eq (v "nu") e)), cs1 @ cs2)
    | Opp e' | Not e' ->
      (* TODO: reflect *)
      (* TODO: rule out invalid cases *)
      let (TRef (tb, q), cs) = f e' in
      (TRef (tb, QExpr (eq (v "nu") e)), cs)
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
        tfun "e" (TRef (TInt, QExpr (leq nu (v "s")))) (
        tfun "body" (
          tfun "i" (z_range (v "s") (v "e")) (
            tfun "x" (TRef (tx_base, inv (v "i") nu))
            (TRef (tx_base, inv (add z1 (v "i")) nu)))) (
        tfun "init" (TRef (tx_base, inv (v "s") nu))
        (TRef (tx_base, inv e nu))))) in 
      check_app g a t_iter [ts; te; tb; tx]
    | Lam (x, t, body) ->
      let (t_body, cs) = typecheck d ((x,t)::g) a body in
      (tfun x t t_body, cs)
    | PCons (es, q_opt) ->
      let (ts, cs_s) = List.map f es |> List.split in
      (tbool, [])
      (* (tprod ts q_opt, cs_s @ (match q_opt with
        | Some (xs, q) -> [CheckCons (List.combine xs ts @ g, a, q)]
        | None -> [])) *)
    | PDestr (e1, xs, e2) ->
      let (t1, cs1) = f e1 in
      (match t1 with
      | TProd (ts, q_opt) ->
        let a' = match q_opt with Some (xs, q) -> [q] | _ -> [] in
        let (t2, cs2) = typecheck d (List.combine xs ts) (a' @ a) e2 in
        (t2, cs1 @ cs2)
      | _ -> failwith "not a product")
    | _ -> todo ()
  in f e

and check_app (g: gamma) (a: alpha) (t_f: typ) (t_args: typ list) : typ * cons list =
  print_endline ("Function: " ^ show_typ t_f);
  print_endline (String.concat "\n" (List.map show_typ t_args));
  match t_args with
  | [] -> (t_f, [])
  | t_arg::t_args' ->
    (match t_f with
    | TFun (x, t_x, t_body) ->
      let (t, cs) = check_app ((x,t_x)::g) a t_body t_args' in
      (t, Subtype (g, a, t_arg, t_x) :: cs)
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
    let q_cons = property |> Option.map (fun q -> CheckCons (g, a, q)) |> Option.to_list in
    cs @ out_cons @ q_cons