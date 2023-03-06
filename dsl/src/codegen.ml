open Ast
open Dsl
open Utils
open Ast_utils

(* circuit declarations *)
type delta = (string * circuit) list

(* existential variables *)
type beta = string list

(* variable environment *)
type gamma = (string * expr) list

(* assertion store *)
type alpha = qual list

let d_empty = []

let a_empty = []

(* fresh var generator *)
let ref_counter = ref 0

let fresh_var prefix () =
  let v = prefix ^ ".v" ^ string_of_int !ref_counter in
  ref_counter := !ref_counter + 1 ;
  v

let add_to_delta (d : delta) (c : circuit) : delta =
  match c with Circuit {name; inputs; outputs; dep; body} -> (name, c) :: d

let add_to_deltas (d : delta) (c : circuit list) =
  List.fold_left add_to_delta d c

(* R1CS format:
   (coeffa_1*vara_1+...+coeffa_n*vara_n) *
   (coeffb_1*varb_1+...+coeffb_n*varb_n) -
   (coeffc_1*varc_1+...+coeffc_n*varc_n) = 0
   , where coeff \in F *)
type coeff = int [@@deriving show]

type r1cs =
  | R1CS of
      (string * coeff) list * (string * coeff) list * (string * coeff) list
[@@deriving show]

let init_gamma_no_val (c : circuit) : string list =
  let get_str = List.map (fun (x, t) -> x) in
  match c with
  | Circuit {name; inputs; outputs; dep; body} ->
      List.rev (get_str outputs) @ List.rev (get_str inputs)

let init_gamma (c : circuit) (args : expr list) : (string * expr) list =
  let init_inputs = List.map2 (fun (x, _) e -> (x, e)) in
  match c with
  | Circuit {name; inputs; outputs; dep; body} ->
      List.rev (init_inputs inputs args)

let rec reify_expr (prefix : string) (g : gamma) (b : beta) (d : delta)
    (a : alpha) (e : expr) : gamma * beta * alpha * expr =
  match e with
  | NonDet ->
      (* generate a fresh var for it *)
      let x = fresh_var prefix () in
      ((x, Var x) :: g, x :: b, a, Var x)
  | CPrime | CPLen | Const _ ->
      (g, b, a, e)
  | Binop (ty, op, e1, e2) ->
      let g', b', a', e1' = reify_expr prefix g b d a e1 in
      let g'', b'', a'', e2' = reify_expr prefix g' b' d a' e2 in
      (g'', b'', a'', Binop (ty, op, e1', e2'))
  | Boolop (op, e1, e2) ->
      let g', b', a', e1' = reify_expr prefix g b d a e1 in
      let g'', b'', a'', e2' = reify_expr prefix g' b' d a' e2 in
      (g'', b'', a'', Boolop (op, e1', e2'))
  | Not e1 ->
      let g', b', a', e1' = reify_expr prefix g b d a e1 in
      (g', b', a', Not e1')
  | Var v ->
      let t =
        match List.assoc_opt v g with
        | Some t ->
            t
        | None ->
            failwith ("No such variable: " ^ v)
      in
      (g, b, a, t)
  | LetIn (x, e1, e2) ->
      let g', b', a', e1' = reify_expr prefix g b d a e1 in
      let g'', b'', a'', e2' = reify_expr prefix ((x, e1') :: g') b' d a e2 in
      (g'', b'', a'', e2')
  | Call (c_name, args) -> (
    match List.assoc_opt c_name d with
    | Some c -> (
        let g', b', a', out_vars = codegen_circuit args g b d a c in
        match out_vars with
        | [out_var] ->
            (g, b', a', Var out_var) (* use original gamma *)
        | _ ->
            failwith "Multiple outputs not supported" )
    | None ->
        failwith ("No such circuit: " ^ c_name) )
  | _ ->
      failwith
        (Format.sprintf "Codegen unavailable for expression %s" (show_expr e))

and codegen_stmt prefix (g : gamma) (b : beta) (d : delta) (a : alpha) (s : stmt)
    : gamma * beta * alpha =
  (* print_endline (Format.sprintf "Codegen for %s" (show_stmt s)) ; *)
  match s with
  | SSkip ->
      (g, b, a)
  | SLet (x, e) ->
      let g', b', a', e' = reify_expr prefix g b d a e in
      ((x, e') :: g', b', a')
  | SAssert (e1, e2) ->
      let g', b', a', e1' = reify_expr prefix g b d a e1 in
      let g'', b'', a'', e2' = reify_expr prefix g' b' d a' e2 in
      (g'', b'', a'' @ [qeq e1' e2'])
  | _ ->
      todos "codegen_stmt"

and codegen_circuit (args : expr list) (g : gamma) (b : beta) (d : delta)
    (a : alpha) (c : circuit) : gamma * beta * alpha * string list =
  match c with
  | Circuit {name; inputs; outputs; dep; body} ->
      let g', b', a', args' =
        List.fold_left
          (fun (g, b, a, args) e ->
            let g', b', a', e' = reify_expr name g b d a e in
            (g', b', a', args @ [e']) )
          (g, b, a, []) args
      in
      (* output: NonDet *)
      let g1 = init_gamma c args' @ g' in
      let out_vars = ref [] in
      let g'', b'', a'' =
        List.fold_left
          (fun (g, b, a) (x, _) ->
            let x' = fresh_var name () in
            out_vars := !out_vars @ [x'] ;
            ((x, Var x') :: g, x' :: b, a) )
          (g1, b', a') (List.rev outputs)
      in
      let g''', b''', a''' =
        List.fold_left
          (fun ((g, b, a) : gamma * beta * alpha) (s : stmt) ->
            codegen_stmt name g b d a s )
          (g'', b'', a'') body
      in
      (g''', b''', a''', !out_vars)

(* R1CS assertion *)
type rexpr =
  | RConst of const [@printer fun fmt c -> fprintf fmt "%s" (show_const c)]
  | RCPrime [@printer fun fmt _ -> fprintf fmt "C.q"]
  | RCPLen [@printer fun fmt _ -> fprintf fmt "C.k"]
  | RVar of string [@printer fun fmt x -> fprintf fmt "%s" x]
  (* unary operation *)
  | ROpp of rexpr [@printer fun fmt e -> fprintf fmt "(- %s)" (show_rexpr e)]
  (* binary operation *)
  | RBinop of rbinop * rexpr * rexpr
      [@printer
        fun fmt (op, e1, e2) ->
          fprintf fmt "(%s %s %s)" (show_rbinop op) (show_rexpr e1)
            (show_rexpr e2)]
  | RComp of rcomp * rexpr * rexpr
      [@printer
        fun fmt (op, e1, e2) ->
          fprintf fmt "(%s %s %s)" (show_rcomp op) (show_rexpr e1)
            (show_rexpr e2)]

and rbinop =
  | RAdd [@printer fun fmt _ -> fprintf fmt "+"]
  | RSub [@printer fun fmt _ -> fprintf fmt "-"]
  | RMul [@printer fun fmt _ -> fprintf fmt "*"]
[@@deriving show]

and rcomp = REq [@printer fun fmt _ -> fprintf fmt "="] [@@deriving show]

type ralpha = rexpr list [@@deriving show]

(* transformation *)
let denote (q : qual) : rexpr option =
  let rec denote_qual (q : qual) : rexpr option =
    match q with QExpr e -> denote_expr e | _ -> None
  and denote_expr (e : expr) : rexpr option =
    match e with
    | Const c ->
        Some (RConst c)
    | CPrime ->
        Some RCPrime
    | CPLen ->
        Some RCPLen
    | Var x ->
        Some (RVar x)
    | Binop (BF, op, e1, e2) -> (
      match (denote_expr e1, denote_expr e2) with
      | Some e1', Some e2' -> (
        match denote_binop op with
        | Some op' ->
            Some (RBinop (op', e1', e2'))
        | None ->
            None )
      | _ ->
          None )
    | Comp (op, e1, e2) -> (
      match (denote_expr e1, denote_expr e2) with
      | Some e1', Some e2' -> (
        match denote_comp op with
        | Some op' ->
            Some (RComp (op', e1', e2'))
        | None ->
            None )
      | _ ->
          None )
    | _ ->
        None
  and denote_binop (op : binop) : rbinop option =
    match op with
    | Add ->
        Some RAdd
    | Sub ->
        Some RSub
    | Mul ->
        Some RMul
    | _ ->
        None
  and denote_comp (op : comp) : rcomp option =
    match op with
    | Eq ->
        Some REq
    | Leq ->
        None
    | Lt ->
        None (* assertions only contain Eq *)
  in
  denote_qual q

let denote_alpha (a : alpha) : ralpha option =
  let rec denote_alpha' (a : alpha) : ralpha option =
    match a with
    | [] ->
        Some []
    | q :: a' -> (
      match denote q with
      | Some q' -> (
        match denote_alpha' a' with
        | Some a'' ->
            Some (q' :: a'')
        | None ->
            None )
      | None ->
          None )
  in
  denote_alpha' a

(* transform rexpr into (rexpr1 , rexpr2, rexpr3), which means rexpr = rexpr1 * rexpr2 + rexpr3 *)
(* let rec transform (e: rexpr) : (rexpr option * rexpr option * rexpr option) =
   match e with
   | RConst _ -> (None, None, Some e)
   | RCPrime -> (None, None, Some e)
   | RCPLen -> (None, None, Some e)
   | RVar _ -> (None, None, Some e)
   | ROpp e' -> (match transform e' with
     | (Some e1, Some e2, Some e3) -> (Some (ROpp e1), Some e2, Some (ROpp e3))
     | _ -> (None, None, None))
   | RBinop (op, e1, e2) -> (match op with
     | RAdd -> (match transform e1, transform e2 with
       | (Some e1', Some e2', Some e3'), (Some e1'', Some e2'', Some e3'') ->
         (Some (RBinop (RAdd, e1', e1'')), Some (RBinop (RAdd, e2', e2'')), Some (RBinop (RAdd, e3', e3'')))
       | _ -> (None, None, None))
     | RSub -> (match transform e1, transform e2 with
       | (Some e1', Some e2', Some e3'), (Some e1'', Some e2'', Some e3'') ->
         (Some (RBinop (RAdd, e1', e1'')), Some (RBinop (RAdd, e2', e2'')), Some (RBinop (RSub, e3', e3'')))
       | _ -> (None, None, None))
     | RMul -> (match transform e1, transform e2 with
       | (Some e1', Some e2', Some e3'), (Some e1'', Some e2'', Some e3'') ->
         (Some (RBinop (RAdd, e1', e1'')), Some (RBinop (RAdd, e2', e2'')), Some (RBinop (RAdd, e3', e3'')))
       | _ -> (None, None, None)))
   | RComp (op, e1, e2) -> (None, None, Some e) *)

let show_gamma (g : gamma) : string =
  let rec show_gamma' (g : gamma) : string =
    match g with
    | [] ->
        ""
    | (x, v) :: g' ->
        Format.sprintf "%s, %s -> %s" (show_gamma' g') x (show_expr v)
  in
  show_gamma' g

let show_beta (b : beta) : string =
  let rec show_beta' (b : beta) : string =
    match b with
    | [] ->
        ""
    | v :: b' ->
        Format.sprintf "%s, %s" (show_beta' b') v
  in
  show_beta' b

let show_rexpr (e : rexpr) : string =
  let rec show_rexpr' (e : rexpr) : string =
    match e with
    | RConst c ->
        show_const c
    | RCPrime ->
        "q"
    | RCPLen ->
        "k"
    | RVar x ->
        x
    | ROpp e' ->
        Format.sprintf "-(%s)" (show_rexpr' e')
    | RBinop (op, e1, e2) -> (
      match op with
      | RAdd ->
          Format.sprintf "(%s) + (%s)" (show_rexpr' e1) (show_rexpr' e2)
      | RSub ->
          Format.sprintf "(%s) - (%s)" (show_rexpr' e1) (show_rexpr' e2)
      | RMul ->
          Format.sprintf "(%s) * (%s)" (show_rexpr' e1) (show_rexpr' e2) )
    | RComp (op, e1, e2) -> (
      match op with
      | REq ->
          Format.sprintf "(%s) = (%s)" (show_rexpr' e1) (show_rexpr' e2) )
  in
  show_rexpr' e

let show_ralpha (a : ralpha) : string =
  let rec show_ralpha' (a : ralpha) : string =
    match a with
    | [] ->
        ""
    | q :: a' ->
        Format.sprintf "%s, %s" (show_ralpha' a') (show_rexpr q)
  in
  show_ralpha' a

let codegen (d : delta) (c : circuit) : r1cs =
  match c with
  | Circuit {name; inputs; outputs; dep; body} -> (
      let args = List.map (fun (x, _) -> NonDet) inputs in
      let g, b, a, out_vars = codegen_circuit args [] [] d [] c in
      match denote_alpha a with
      | Some a' ->
          print_endline (Format.sprintf "=============================") ;
          print_endline (Format.sprintf "circuit: %s" name) ;
          print_endline
            (Format.sprintf "variable environment: %s" (show_gamma g)) ;
          print_endline (Format.sprintf "R1CS variables: %s" (show_beta b)) ;
          print_endline (Format.sprintf "Rconstraints: %s" (show_ralpha a')) ;
          print_endline (Format.sprintf "=============================") ;
          R1CS ([], [], [])
      | None ->
          failwith "codegen: failed to codegen circuit" )
