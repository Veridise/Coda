open Ast
open Dsl
open Utils
open Ast_utils
open R1cs_utils

(* circuit declarations *)
type delta = (string * circuit) list

(* existential variables *)
type beta = string list

(* variable environment *)
type gamma = (string * expr) list

(* assertion store *)
type alpha = qual list

(* r1cs *)
type r1cs_algebra = arithmetic_expression list

(* circuit configuration *)
type configuration = (string * int) list

let d_empty = []

let a_empty = []

(* fresh var generator *)
let ref_counter = ref 0

let fresh_var prefix () =
  let v = prefix ^ ".v" ^ string_of_int !ref_counter in
  ref_counter := !ref_counter + 1 ;
  v

let add_to_delta (d : delta) (c : circuit) : delta =
  match c with Circuit {name; _} -> (name, c) :: d

let add_to_deltas (d : delta) (c : circuit list) =
  List.fold_left add_to_delta d c

let init_gamma_no_val (c : circuit) : string list =
  let get_str = List.map (fun (x, _) -> x) in
  match c with
  | Circuit {inputs; outputs; _} ->
      List.rev (get_str outputs) @ List.rev (get_str inputs)

let init_gamma (c : circuit) (args : expr list) : (string * expr) list =
  let init_inputs = List.map2 (fun (x, _) e -> (x, e)) in
  match c with Circuit {inputs; _} -> List.rev (init_inputs inputs args)

let rec reify_expr (prefix : string) (g : gamma) (b : beta) (d : delta)
    (a : alpha) (config : configuration) (e : expr) :
    gamma * beta * alpha * expr =
  match e with
  | NonDet ->
      (* generate a fresh var for it *)
      let x = fresh_var prefix () in
      ((x, Var x) :: g, x :: b, a, Var x)
  | CPrime | CPLen | Const _ ->
      (g, b, a, e)
  | Binop (ty, op, e1, e2) ->
      let g', b', a', e1' = reify_expr prefix g b d a config e1 in
      let g'', b'', a'', e2' = reify_expr prefix g' b' d a' config e2 in
      (g'', b'', a'', Binop (ty, op, e1', e2'))
  | Boolop (op, e1, e2) ->
      let g', b', a', e1' = reify_expr prefix g b d a config e1 in
      let g'', b'', a'', e2' = reify_expr prefix g' b' d a' config e2 in
      (g'', b'', a'', Boolop (op, e1', e2'))
  | Not e1 ->
      let g', b', a', e1' = reify_expr prefix g b d a config e1 in
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
      let g', b', a', e1' = reify_expr prefix g b d a config e1 in
      let g'', b'', a'', e2' =
        reify_expr prefix ((x, e1') :: g') b' d a' config e2
      in
      (g'', b'', a'', e2')
  | Call (c_name, args) -> (
    match List.assoc_opt c_name d with
    | Some c -> (
        let _, b', a', out_vars, _ = codegen_circuit args g b d a config c in
        match out_vars with
        | [out_var] ->
            (g, b', a', Var out_var) (* use original gamma *)
        | _ ->
            failwith "Multiple outputs not supported"
        (* TODO: add support for multiple outputs (tuple) *) )
    | None ->
        failwith ("No such circuit: " ^ c_name) )
  | Assert (e1, e2) ->
      let g', b', a', e1' = reify_expr prefix g b d a config e1 in
      let g'', b'', a'', e2' = reify_expr prefix g' b' d a' config e2 in
      (g'', b'', a'' @ [qeq e1' e2'], NonDet)
  | _ ->
      failwith
        (Format.sprintf "Codegen unavailable for expression %s" (show_expr e))

and codegen_circuit (args : expr list) (g : gamma) (b : beta) (d : delta)
    (a : alpha) (config : configuration) (c : circuit) :
    gamma * beta * alpha * string list * expr =
  match c with
  | Circuit {name; outputs; body; _} ->
      let g', b', a', args' =
        List.fold_left
          (fun (g, b, a, args) e ->
            let g', b', a', e' = reify_expr name g b d a config e in
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
      let g''', b''', a''', final_e =
        reify_expr name g'' b'' d a'' config body
      in
      (g''', b''', a''', !out_vars, final_e)

(* R1CS assertion *)
(* Note: this is not a general R1CS assertion, but a special one that
   is used in the codegen i.e. R1CS middle level IR *)
type rexpr =
  | RConst of int [@printer fun fmt c -> fprintf fmt "%s" (string_of_int c)]
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

(* transformation from qual to rexpr (R1CS assertion) *)
let denote (q : qual) : rexpr option =
  let rec denote_qual (q : qual) : rexpr option =
    match q with QExpr e -> denote_expr e | _ -> None
  and denote_expr (e : expr) : rexpr option =
    match e with
    | Const (CF i) ->
        Some (RConst i)
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

(* simplification of R1CS assertions *)
let rec simplify (e : rexpr) : rexpr =
  match e with
  | RConst _ ->
      e
  | RCPrime ->
      e
  | RCPLen ->
      e
  | RVar _ ->
      e
  | ROpp e' ->
      ROpp (simplify e')
  | RBinop (op, e1, e2) -> (
    match (simplify e1, simplify e2) with
    | RConst c1, RConst c2 -> (
      match op with
      | RAdd ->
          RConst (c1 + c2)
      | RSub ->
          RConst (c1 - c2)
      | RMul ->
          RConst (c1 * c2) )
    | RConst 0, e2' -> (
      match op with
      | RAdd ->
          e2' (* 0 + x -> x *)
      | RSub ->
          ROpp e2' (* 0 - x -> -x *)
      | RMul ->
          RConst 0 (* 0 * x -> 0 *) )
    | e1', RConst 0 -> (
      match op with
      | RAdd ->
          e1' (* x + 0 -> x *)
      | RSub ->
          e1' (* x - 0 -> x *)
      | RMul ->
          RConst 0 (* x * 0 -> 0 *) )
    | RConst 1, e2' -> (
      match op with RMul -> e2' (* 1 * x -> x *) | _ -> RBinop (op, e1, e2') )
    | e1', RConst 1 -> (
      match op with
      | RMul ->
          e1' (* x * 1 -> x *)
      | _ ->
          RBinop (op, e1', RConst 1) )
    | e1', e2' ->
        if e1' = e2' then
          match op with
          | RAdd ->
              RBinop (RMul, RConst 2, e1') (* x + x -> 2 * x *)
          | RSub ->
              RConst 0 (* x - x -> 0 *)
          | RMul ->
              RBinop (RMul, e1', e2')
        else RBinop (op, e1', e2') )
  | RComp (op, e1, e2) ->
      RComp (op, simplify e1, simplify e2)

let simplify_alpha (a : ralpha) : ralpha = List.map simplify a

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
        string_of_int c
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

let show_list_signal (l : signal list) : string =
  let rec show_list_signal' (l : signal list) : string =
    match l with
    | [] ->
        ""
    | x :: [] ->
        Format.sprintf "%s" (fst x)
    | x :: l' ->
        Format.sprintf "%s , %s" (fst x) (show_list_signal' l')
  in
  show_list_signal' l

(* transform rexpr into r1cs arithmetic_expression *)
let rec transform (e : rexpr) : arithmetic_expression =
  match e with
  | RConst c ->
      Number (Big_int.big_int_of_int c)
  | RCPrime ->
      failwith "transform: RCPrime"
  | RCPLen ->
      failwith "transform: RCPLen"
  | RVar x ->
      Signal x
  | ROpp e' ->
      R1cs_utils.simplify (opp (transform e'))
  | RBinop (op, e1, e2) -> (
    match op with
    | RAdd ->
        let e1' = transform e1 in
        let e2' = transform e2 in
        R1cs_utils.simplify (add e1' e2')
    | RSub ->
        let e1' = transform e1 in
        let e2' = transform e2 in
        R1cs_utils.simplify (sub e1' e2')
    | RMul ->
        let e1' = transform e1 in
        let e2' = transform e2 in
        R1cs_utils.simplify (mul e1' e2') )
  | RComp (REq, e1, e2) ->
      let e1' = transform e1 in
      let e2' = transform e2 in
      R1cs_utils.simplify (sub e1' e2')

let rec show_list_r1cs (e : r1cs list) : string =
  match e with
  | [] ->
      ""
  | e' :: e'' ->
      Format.sprintf "%s\n%s" (show_r1cs e') (show_list_r1cs e'')

let find_in_gamma (x : symbol) (g : gamma) : symbol =
  match List.assoc_opt x g with Some (Var v) -> v | _ -> x

let humanify_arithmetic_expression (e : arithmetic_expression)
    (signals : signal list) (g : gamma) : arithmetic_expression =
  let tasks : (symbol * symbol) list =
    List.map (fun (x, _) -> (find_in_gamma x g, x)) signals
  in
  List.fold_left (fun e (x, v) -> subst_var e x v) e tasks

(* bind the i/o signals to their corresponding readable names *)
let humanify (a : r1cs_algebra) (signals : signal list) (g : gamma) :
    r1cs_algebra =
  List.map
    (fun (e : arithmetic_expression) ->
      humanify_arithmetic_expression e signals g )
    a

let circuit_io_list (c : circuit) : signal list * signal list =
  match c with Circuit {inputs; outputs; _} -> (inputs, outputs)

(* generate r1cs from circuit *)
let codegen (d : delta) (config : configuration) (c : circuit) : unit =
  match c with
  | Circuit {name; inputs; outputs; _} -> (
      let args = List.map (fun (_, _) -> NonDet) inputs in
      let g, _, a, _, _ = codegen_circuit args [] [] d [] config c in
      match denote_alpha a with
      | Some a' ->
          let simplify_a = simplify_alpha a' in
          let transform_a = List.map transform simplify_a in
          let humanify_a = humanify transform_a (inputs @ outputs) g in
          let r1cs_a = List.map r1cs_of_arithmetic_expression humanify_a in
          print_endline (Format.sprintf "=============================") ;
          print_endline
            (Format.sprintf "Circuit: %s   Input: %s   Output: %s" name
               (show_list_signal inputs) (show_list_signal outputs) ) ;
          (* print_endline
               (Format.sprintf "variable environment: %s" (show_gamma g)) ;
             print_endline (Format.sprintf "R1CS variables: %s" (show_beta b)) ; *)
          print_endline (Format.sprintf "R1CS:\n%s" (show_list_r1cs r1cs_a)) ;
          print_endline (Format.sprintf "=============================") ;
          ref_counter := 0
      | None ->
          failwith "codegen: failed to codegen circuit" )
