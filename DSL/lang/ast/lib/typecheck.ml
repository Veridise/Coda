open Ast
open Dsl
open Utils

(* circuit declarations *)
type delta = (string * circuit) list [@@deriving show]

(* typing environment *)
type gamma = (string * typ) list [@@deriving show]

(* assertion store *)
type alpha = qual list [@@deriving show]

let d_empty = []

let g_empty = []

let a_empty = []

let add_to_delta (d: delta) (c: circuit) : delta =
  match c with
  | Circuit {name; inputs; outputs; exists; ctype; body} -> (name, c) :: d

type cons = 
  | Subtype of gamma * alpha * typ * typ
    [@printer fun fmt (g,a,t1,t2) -> fprintf fmt "Gamma:\n%s\nAlpha:\n%s\n---Subtype---\n%s <: %s" (show_gamma g) (show_alpha a) (show_typ t1) (show_typ t2)]
  | HasType of gamma * alpha * string * typ
    [@printer fun fmt (g,a,x,t) -> fprintf fmt "Gamma:\n%s\nAlpha:\n%s\n---Type---\n%s : %s" (show_gamma g) (show_alpha a) x (show_typ t)]
  | CheckCons of gamma * alpha * qual 
    [@printer fun fmt (g,a,q) -> fprintf fmt "Gamma:\n%s\nAlpha:\n%s\n---Constrain---\n%s" (show_gamma g) (show_alpha a) (show_qual q)]
  [@@deriving show]

let pc (cs: cons list) : unit =
  cs |> List.map show_cons |> String.concat "\n\n" |> print_endline

let functionalize_circ (Circuit {name; inputs; outputs; exists; ctype; body}) : typ =
  ctype
  (* let get_typ (_,t) = t in
  let get_name (x,_) = x in
  assert (List.length outputs = 1);
  List.fold_right (uncurry tfun) inputs (get_typ (List.hd outputs)) *)

let rec subtype (g: gamma) (a: alpha) (t1: typ) (t2: typ) : cons list =
  match (t1, t2) with
  | (TRef _, TRef _) -> [Subtype (g, a, t1, t2)]
  | (TFun (x,t1,ft2), TFun (y,t1',ft2')) ->
    Subtype (g, a, t1', t1) :: subtype ((x,t1')::g) a (ft2 (v x)) (ft2' (v x))
  | (TTuple ts1, TTuple ts2) -> List.concat_map (uncurry (subtype g a)) (List.combine ts1 ts2)
  | (TDProd _, TDProd _) -> failwith "TODO: product subtyping"
  | (TArr _, TArr _) -> failwith "TODO: array subtyping"
  | _ -> failwith ("Subtype: illegal subtype " ^ (show_typ t1) ^ (show_typ t2))

let coerce_psingle : typ -> typ = function
  | TTuple [t] -> t
  | t -> t

let rec synthesize (d: delta) (g: gamma) (a: alpha) (e: expr) : (typ * cons list) = 
  print_endline (Format.sprintf "Synthesizing type for %s" (show_expr e));
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
    | Ascribe (e, t) ->
      let cs = check d g a e t in (t, cs)
    | LamA (x, t1, e) ->
      let (t2, cs) = synthesize d ((x,t1)::g) a e in
      (tfun x t1 (fun xe -> subst_typ x xe t2), cs)
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
    | Call (c_name, args) ->
      (match List.assoc_opt c_name d with
      | Some c -> 
        let (t_out, cs_out) = check_app d g a (functionalize_circ c) args in
        (t_out, cs_out)
      | None -> failwith ("No such circuit: " ^ c_name))
    | Iter {s; e; body; init; inv} ->
      let (tx, cx) = f init in
      (* s is int *)
      let t_iter = 
        (* TODO: ensure var freshness *)
        tfun "s" tint (fun s ->
        tfun "e" (TRef (TInt, QExpr (leq (v "s") nu))) (fun e ->
        tfun "body" (
          (* assume s <= i <= e *)
          tfun "i" (z_range s e) (fun i ->
          (* assume inv(i,x) holds *)
          tfun "x" (inv i nu) (fun _ ->
          (* prove inv(i+1,output) holds *)
          (inv (add z1 i) nu)))) (fun _ ->
        (* prove inv(s,init) holds *)
        tfun "init" (inv (v "s") nu) (fun _ ->
        (* conclude inv(e,output) holds *)
        (inv e nu))))) in 
      check_app d g a t_iter [s; e; body; init]
    | TMake es ->
      let (ts, cs_s) = List.(map f es |> split) in
      (ttuple ts, List.concat cs_s)
    | TGet (e, n) ->
      let (t, cs) = f e in
      (match t with
      | TTuple ts -> 
        if 0 <= n && n < List.length ts then
          (List.nth ts n, cs)
        else
          failwith "Tuple access out of bounds"
      | _ -> failwith "Synthesize: expect tuple type")
    | ArrayOp (Cons, e1, e2) ->
      todos "ArrayOp: Cons"
      (* let (t1, cs1) = f e1 in
      let (TArr (t2, q, e), cs2) = f e2 in
      (TArr (t2, fun nu -> q (drop z1 nu), add e z1), cs1 @ cs2 @ [subtype g a t1 t2]) *)
    | ArrayOp (Get, e1, e2) ->
      todos "ArrayOp: Get"
      (* let (TArr (t1, q, e), cs1) = f e1 in
      let (t2, cs2) = f e2 in
      todo () *)
      (* t1 augmented with v = e1[e2] *)
    (* | DPCons (es, q_opt) ->
      todos "DPCons"
      (* let (ts, cs_s) = List.map f es |> List.split in
      let cs_q = Option.(q_opt |> map (fun (_, q) -> CheckCons (g, a, q es)) |> to_list) in
      (tprod ts q_opt, List.concat cs_s @ cs_q) *)
    | DPDestr (e1, xs, e2) ->
      todos "DPDestr"
      (* let (t1, cs1) = f e1 in
      (match t1 with
      | TDProd (ts, q_opt) ->
        let a' = Option.(q_opt |> map (fun (xs, q) -> q (List.map v xs)) |> to_list) in
        let (t2, cs2) = typecheck d (List.combine xs ts) (a' @ a) e2 in
        (t2, cs1 @ cs2)
      | _ -> failwith "not a product") *) *)
    | _ -> failwith (Format.sprintf "Synthesis unavailable for expression %s" (show_expr e))
  in f e

and check_app (d: delta) (g: gamma) (a: alpha) (t: typ) (es: expr list) : typ * cons list =
  match es with
  | [] -> (t, [])
  | e::es' ->
    (match t with
    | TFun (x, t1, ft2) ->
      let (t, cs) = check_app d ((x,t1)::g) a (ft2 (v x)) es' in
      (t, check d g a e t1 @ cs)
    | _ -> failwith "Not a function")

and check (d: delta) (g: gamma) (a: alpha) (e: expr) (t: typ) : cons list =
  print_endline (Format.sprintf "Checking %s has type %s" (show_expr e) (show_typ t));
  match (e, t) with
  | (Lam (x, body), TFun (y, t1, ft2)) ->
      check d ((x,t1)::g) a body (ft2 (v x))
  | (LamA (x, t, body), TFun (y, t1, ft2)) -> 
      subtype g a t1 t @ check d ((x,t1)::g) a body (ft2 (v x))

  | (LetIn (x, e1, e2), t2) ->
    let (t1, cs) = synthesize d g a e1 in
    check d ((x,t1)::g) a e2 t2
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
  | SAssert e ->
    let _ = check d g a e tbool in
    (g, [QExpr e], [])

let rec to_base_typ = function
  | TRef (tb, _) -> TRef (tb, QTrue)
  | TArr (t,_,n) -> TArr (to_base_typ t, (fun _ -> QTrue), n)
  | TFun _ -> todos "to_base_typ: TFun"
  | TTuple _ -> todos "to_base_typ: TTuple"
  | TDProd _ -> todos "to_base_typ: TDProd"
  [@@deriving show]
  
let init_gamma (c: circuit) : gamma =
  let to_base_types = List.map (fun (x,t) -> (x, to_base_typ t)) in
  match c with
  | Circuit {name; inputs; outputs; exists; ctype; body} ->
    inputs @ to_base_types outputs @ to_base_types exists

let typecheck_circuit (d: delta) (c: circuit) : cons list =
  match c with
  | Circuit {name; inputs; outputs; exists; ctype; body} ->
    let (g, a, cs) = List.fold_left
      (fun ((g, a, cs): gamma * alpha * cons list) (s: stmt) ->
        let (g', a', cs') = typecheck_stmt d g a s in 
        (g', a @ a', cs @ cs'))
      (init_gamma c, [], [])
      body in
    assert (List.length outputs = 1);
    let out_cons = List.map (fun (x,t) -> HasType (g, a, x, t)) outputs in
    let vars_in = inputs |> List.map (fun (x,_) -> x) |> List.map v in
    let vars_out = outputs |> List.map (fun (x,_) -> x) |> List.map v in
    cs @ out_cons