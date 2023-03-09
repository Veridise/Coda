open Ast
open Dsl
open Utils

(* circuit declarations *)
type delta = (string * circuit) list [@@deriving show]

(* existential variables *)
type beta = string list [@@deriving show]

(* variable environment *)
type gamma = (string * expr) list [@@deriving show]

(* assertion store *)
type alpha = qual list [@@deriving show]

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
  | Opp e1 ->
      let g', b', a', e1' = reify_expr prefix g b d a e1 in
      (g', b', a', Opp e1')
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
            (g, b', a', Var out_var (* use original gamma *))
        | _ ->
            failwith "Multiple outputs not supported" )
    | None ->
        failwith ("No such circuit: " ^ c_name) )
  | _ ->
      failwith
        (Format.sprintf "Codegen unavailable for expression %s" (show_expr e))

and codegen_stmt prefix (g : gamma) (b : beta) (d : delta) (a : alpha) (s : stmt)
    : gamma * beta * alpha =
  print_endline (Format.sprintf "Codegen for %s" (show_stmt s)) ;
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

let codegen (d : delta) (c : circuit) : r1cs =
  match c with
  | Circuit {name; inputs; outputs; dep; body} ->
      let args = List.map (fun (x, _) -> NonDet) inputs in
      let g, b, a, out_vars = codegen_circuit args [] [] d [] c in
      print_endline (Format.sprintf "=============================") ;
      print_endline (Format.sprintf "circuit: %s" name) ;
      print_endline (Format.sprintf "variable environment: %s" (show_gamma g)) ;
      print_endline (Format.sprintf "R1CS variables: %s" (show_beta b)) ;
      print_endline (Format.sprintf "constraints: %s" (show_alpha a)) ;
      print_endline (Format.sprintf "=============================") ;
      R1CS ([], [], [])
