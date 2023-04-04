open Ast
open Dsl
open Utils
open Ast_utils
open R1cs_utils
open Big_int_Z

(* circuit declarations *)
type delta = (string * circuit) list

(* existential variables *)
type beta = string list

(* variable environment *)
type gamma = (string * expr) list

(* circuit environment *)
type interp = (string * int) list

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

(* R1CS assertion *)
(* Note: this is not a general R1CS assertion, but a special one that
   is used in the codegen i.e. R1CS middle level IR *)
type rexpr =
  | RConst of big_int
      [@printer fun fmt c -> fprintf fmt "%s" (string_of_big_int c)]
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
let rec denote_expr (e : expr) : rexpr option =
  match e with
  | Const (CF i) ->
      Some (RConst i)
  | Const (CInt i) ->
      Some (RConst i)
  | CPrime ->
      None
  | CPLen ->
      None
  | Fn (ToUZ, [e]) ->
      denote_expr e
  | Var x ->
      Some (RVar x)
  | Binop (_, op, e1, e2) -> (
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

let denote (q : qual) : rexpr option =
  let rec denote_qual (q : qual) : rexpr option =
    match q with QExpr e -> denote_expr e | _ -> None
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
  | RVar _ ->
      e
  | ROpp e' ->
      ROpp (simplify e')
  | RBinop (op, e1, e2) -> (
    match (simplify e1, simplify e2) with
    | RConst c1, RConst c2 -> (
      match op with
      | RAdd ->
          RConst (add_big_int c1 c2)
      | RSub ->
          RConst (sub_big_int c1 c2)
      | RMul ->
          RConst (mult_big_int c1 c2) )
    | RConst c, e2' ->
        if eq_big_int zero_big_int c then
          match op with
          | RAdd ->
              e2' (* 0 + x -> x *)
          | RSub ->
              ROpp e2' (* 0 - x -> -x *)
          | RMul ->
              RConst zero_big_int (* 0 * x -> 0 *)
        else if eq_big_int unit_big_int c then
          match op with
          | RMul ->
              e2' (* 1 * x -> x *)
          | _ ->
              RBinop (op, e1, e2')
        else RBinop (op, RConst c, e2')
    | e1', RConst z ->
        if eq_big_int zero_big_int z then
          match op with
          | RAdd ->
              e1' (* x + 0 -> x *)
          | RSub ->
              e1' (* x - 0 -> x *)
          | RMul ->
              RConst zero_big_int (* x * 0 -> 0 *)
        else if eq_big_int unit_big_int z then
          match op with
          | RMul ->
              e1' (* x * 1 -> x *)
          | _ ->
              RBinop (op, e1', RConst unit_big_int)
        else RBinop (op, e1', RConst z)
    | e1', e2' ->
        if e1' = e2' then
          match op with
          | RAdd ->
              RBinop (RMul, RConst (big_int_of_int 2), e1') (* x + x -> 2 * x *)
          | RSub ->
              RConst zero_big_int (* x - x -> 0 *)
          | RMul ->
              RBinop (RMul, e1', e2')
        else RBinop (op, e1', e2') )
  | RComp (op, e1, e2) ->
      RComp (op, simplify e1, simplify e2)

let simplify_ralpha (a : ralpha) : ralpha = List.map simplify a

let rec get_nth_array (l : expr) (n : int) : expr =
  match l with
  | ArrayOp (Cons, [e1; e2]) ->
      if n = 0 then e1 else get_nth_array e2 (n - 1)
  | Const CNil ->
      failwith "get_nth_array: index out of bounds"
  | _ ->
      failwith ("get_nth_array: not an array :" ^ show_expr l)

let rec length_of (l : expr) : int =
  match l with ArrayOp (Cons, [_; e2]) -> 1 + length_of e2 | _ -> 0

let rec take_array (l : expr) (n : int) : expr =
  match l with
  | ArrayOp (Cons, [e1; e2]) ->
      if n = 0 then Const CNil else ArrayOp (Cons, [e1; take_array e2 (n - 1)])
  | _ ->
      failwith ("take_array: not an array :" ^ show_expr l)

let rec concat_array (l1 : expr) (l2 : expr) : expr =
  match l1 with
  | ArrayOp (Cons, [e1; e2]) ->
      ArrayOp (Cons, [e1; concat_array e2 l2])
  | Const CNil ->
      l2
  | _ ->
      failwith ("concat_array: not an array :" ^ show_expr l1)

let rec drop_array (l : expr) (n : int) : expr =
  match l with
  | ArrayOp (Cons, [_; e2]) ->
      if n = 0 then l else drop_array e2 (n - 1)
  | _ ->
      failwith ("drop_array: not an array :" ^ show_expr l)

(* codegen *)

let rec reify_expr (prefix : string) (g : gamma) (b : beta) (d : delta)
    (a : ralpha) (config : configuration) (e : expr) :
    gamma * beta * ralpha * expr =
  (* print_endline ("Reify: " ^ show_expr e) ; *)
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
        | None -> (
          (* try ... catch *)
          try Const (CF (eval_int e config)) with _ -> e )
      in
      (g, b, a, t)
  | LetIn (x, e1, e2) ->
      let g', b', a', e1' = reify_expr prefix g b d a config e1 in
      let g'', b'', a'', e2' =
        reify_expr prefix ((x, simplify_expr e1') :: g') b' d a' config e2
      in
      (g'', b'', a'', e2')
  | Call (c_name, args) -> (
    match List.assoc_opt c_name d with
    | Some (Circuit {name; inputs; outputs; dep; body}) ->
        let config', args', inputs' = calc_inputs config args inputs in
        let _, b', a', _, return_e =
          codegen_circuit args' g b d a config'
            (Circuit {name; inputs= inputs'; outputs; dep; body})
        in
        (g, b', a', return_e)
    | None ->
        failwith ("No such circuit: " ^ c_name) )
  | Ascribe (e1, _) ->
      let g', b', a', e1' = reify_expr prefix g b d a config e1 in
      (g', b', a', e1')
  | AscribeUnsafe (e1, _) ->
      let g', b', a', e1' = reify_expr prefix g b d a config e1 in
      (g', b', a', e1')
  | Assert (e1, e2) -> (
      let g', b', a', e1' = reify_expr prefix g b d a config e1 in
      let g'', b'', a'', e2' = reify_expr prefix g' b' d a' config e2 in
      match denote_expr (simplify_expr e1') with
      (* pow is handled in simplify_expr *)
      | Some e1'' -> (
        match denote_expr (simplify_expr e2') with
        | Some e2'' ->
            ( g''
            , b''
            , a'' @ [RComp (REq, simplify e1'', simplify e2'')]
            , Const CUnit )
        | None ->
            failwith
              ( "Assert: second argument is invalid"
              ^ show_expr (simplify_expr e2') ) )
      | None ->
          failwith
            ("Assert: first argument is invalid" ^ show_expr (simplify_expr e1'))
      )
  | Lam (_, _) ->
      (g, b, a, e)
  | LamA (x, _, e) ->
      (g, b, a, Lam (x, e)) (* type is erased *)
  | App (e1, e2) -> (
      let g', b', a', e1' = reify_expr prefix g b d a config e1 in
      match e1' with
      | Lam (x, e) ->
          let g'', b'', a'', e2' = reify_expr prefix g' b' d a' config e2 in
          (* evaluate e2 *)
          let e2'' =
            simplify_expr e2' (* simplify e2 before add it to environment*)
          in
          (* substitute x with e2 in e *)
          let g''' = (x, e2'') :: g'' in
          (* add x -> e2 to gamma *)
          let g'''', b'''', a'''', e''' =
            reify_expr prefix g''' b'' d a'' config e
          in
          (* evaluate e *)
          (g'''', b'''', a'''', e''')
      | _ ->
          failwith ("Not a lambda" ^ show_expr e1') )
  | TMake liste ->
      ( g
      , b
      , a
      , TMake
          (List.map
             (fun x ->
               match reify_expr prefix g b d a config x with _, _, _, e' -> e'
               )
             liste ) )
  | TGet (e1, e2) -> (
      let g', b', a', e1' = reify_expr prefix g b d a config e1 in
      match e1' with
      | TMake liste -> (
          let x = List.nth_opt liste e2 in
          match x with
          | Some x' ->
              (g', b', a', x')
          | None ->
              failwith
                ("Index out of bounds" ^ show_expr e1' ^ "." ^ string_of_int e2)
          )
      | _ ->
          failwith ("Not a tuple" ^ show_expr e1') )
  | Push e ->
      let g', b', a', e' = reify_expr prefix g b d a config e in
      (g', b', a', e')
  | Pull e ->
      let g', b', a', e' = reify_expr prefix g b d a config e in
      (g', b', a', e')
  | ArrayOp (Get, [e; i]) ->
      let g, b, a, l = reify_expr prefix g b d a config e in
      (* get i''-th element of l *)
      let g', b', a', i' = reify_expr prefix g b d a config i in
      let i'' = eval_int i' config in
      (* print_endline ("get " ^ string_of_big_int i'');
         print_endline (show_expr l); *)
      (g', b', a', get_nth_array l (int_of_big_int i''))
  | ArrayOp (Cons, [e1; e2]) ->
      let g, b, a, e1' = reify_expr prefix g b d a config e1 in
      let g', b', a', e2' = reify_expr prefix g b d a config e2 in
      (g', b', a', ArrayOp (Cons, [e1'; e2']))
  | ArrayOp (Zip, [e1; e2]) ->
      let g, b, a, e1' = reify_expr prefix g b d a config e1 in
      let g', b', a', e2' = reify_expr prefix g b d a config e2 in
      let g'', b'', a'', ziped_expr =
        expr_array_zip prefix g' b' d a' config e1' e2'
      in
      (g'', b'', a'', ziped_expr)
  | ArrayOp (Take, [n; e]) ->
      let g, b, a, n' = reify_expr prefix g b d a config n in
      let g', b', a', e' = reify_expr prefix g b d a config e in
      let n'' = eval_int n' config in
      (g', b', a', take_array e' (int_of_big_int n''))
  | ArrayOp (Drop, [n; e]) ->
      let g, b, a, n' = reify_expr prefix g b d a config n in
      let g', b', a', e' = reify_expr prefix g b d a config e in
      let n'' = eval_int n' config in
      (g', b', a', drop_array e' (int_of_big_int n''))
  | ArrayOp (Concat, [xs1; xs2]) ->
      let g, b, a, xs1' = reify_expr prefix g b d a config xs1 in
      let g', b', a', xs2' = reify_expr prefix g b d a config xs2 in
      (g', b', a', concat_array xs1' xs2')
  | ArrayOp (Length, [e]) ->
      let g, b, a, e' = reify_expr prefix g b d a config e in
      (g, b, a, Const (CInt (big_int_of_int (length_of e'))))
  | Map (e1, e2) ->
      let g, b, a, e2' = reify_expr prefix g b d a config e2 in
      (* e2' is an array *)
      let e2_out = ref [] in
      let length = length_of e2' in
      let g' = ref g in
      let b' = ref b in
      let a' = ref a in
      for i = 0 to length - 1 do
        let e2_nth = get_nth_array e2' i in
        let _, _, a, e1' =
          reify_expr prefix !g' !b' d !a' config (App (e1, e2_nth))
        in
        (* g' := g;
           b' := b; *)
        a' := a ;
        e2_out := !e2_out @ [e1']
      done ;
      (!g', !b', !a', const_array_untyped !e2_out)
  | Iter {s; e; body; init; _} ->
      (* s: start; e: end;  [start, end) *)
      (*  it's like a for loop *)
      (* t := init;
         for i:= start to end-1 do begin
           t := body i t;
         end
      *)
      let g', b', a', starte = reify_expr prefix g b d a config s in
      let start = eval_int starte config in
      let g'', b'', a'', ende = reify_expr prefix g' b' d a' config e in
      let end_ = eval_int ende config in
      let temp = ref init in
      let g''' = ref g'' in
      let b''' = ref b'' in
      let a''' = ref a'' in
      for i = int_of_big_int start to int_of_big_int end_ - 1 do
        let _, _, a', bodye =
          reify_expr prefix !g''' !b''' d !a''' config
            (App (App (body, Const (CInt (big_int_of_int i))), !temp))
        in
        (* g''' := g' ;
           b''' := b' ; *)
        a''' := a' ;
        temp := bodye
      done ;
      (!g''', !b''', !a''', !temp)
  | Fn (ToUZ, [e]) ->
      (g, b, a, Const (CInt (eval_int e config)))
  | _ ->
      failwith
        (Format.sprintf "Codegen unavailable for expression %s" (show_expr e))

and eval_int (e : expr) (config : configuration) : big_int =
  (* print_endline ("eval_int: " ^ show_expr e) ; *)
  match e with
  | Const (CF f) ->
      f
  | Const (CInt i) ->
      i
  | Const (CBool b) ->
      if b then unit_big_int else zero_big_int
  | Var v -> (
    match List.assoc_opt v config with
    | Some i ->
        big_int_of_int i
    | _ ->
        failwith
          ("No such var as loop bound in the configuration: " ^ show_expr e) )
  | Binop (_, op, e1, e2) -> (
      let i1 = eval_int e1 config in
      let i2 = eval_int e2 config in
      match op with
      | Add ->
          add_big_int i1 i2
      | Sub ->
          sub_big_int i1 i2
      | Mul ->
          mult_big_int i1 i2
      | Mod ->
          mod_big_int i1 i2
      | Pow ->
          power_big_int_positive_int i1 (int_of_big_int i2) )
  | Fn (ToUZ, [e]) ->
      eval_int e config
  | _ ->
      failwith ("Not a constant integer as loop bound: " ^ show_expr e)

and expr_array_zip prefix g b d a config e1 e2 =
  match (e1, e2) with
  | ArrayOp (Cons, [e1; e2]), ArrayOp (Cons, [e1'; e2']) ->
      let g', b', a', e1'' = reify_expr prefix g b d a config e1 in
      let g'', b'', a'', e1''' = reify_expr prefix g' b' d a' config e1' in
      let g''', b''', a''', e2'' =
        expr_array_zip prefix g'' b'' d a'' config e2 e2'
      in
      (g''', b''', a''', ArrayOp (Cons, [TMake [e1''; e1''']; e2'']))
  | Const CNil, Const CNil ->
      (g, b, a, Const CNil)
  | _ ->
      raise
        (Failure ("expr_array_zip: not an array" ^ show_expr e1 ^ show_expr e2))

and simplify_expr (e : expr) : expr =
  (* print_endline ("simplify_expr: " ^ show_expr e) ; *)
  match e with
  | Binop (ty, op, e1, e2) -> (
    match (simplify_expr e1, simplify_expr e2) with
    | Const c1, Const c2 -> (
        let c1 = eval_int (Const c1) [] in
        let c2 = eval_int (Const c2) [] in
        match op with
        | Add ->
            Const (CF (add_big_int c1 c2))
        | Sub ->
            Const (CF (sub_big_int c1 c2))
        | Mul ->
            Const (CF (mult_big_int c1 c2))
        | Pow ->
            Const (CF (power_big_int_positive_int c1 (int_of_big_int c2)))
        | Mod ->
            Const (CF (mod_big_int c1 c2)) )
    | Const (CF c), e2' ->
        if eq_big_int c zero_big_int then
          match op with
          | Add ->
              e2' (* 0 + x -> x *)
          | Mul ->
              Const (CF zero_big_int) (* 0 * x -> 0 *)
          | _ ->
              Binop (ty, op, Const (CF c), e2')
        else if eq_big_int c unit_big_int then
          match op with
          | Mul ->
              e2' (* 1 * x -> x *)
          | _ ->
              Binop (ty, op, Const (CF c), e2')
        else Binop (ty, op, Const (CF c), e2')
    | e1', Const (CF c) ->
        if eq_big_int c zero_big_int then
          match op with
          | Add ->
              e1' (* x + 0 -> x *)
          | Sub ->
              e1' (* x - 0 -> x *)
          | Mul ->
              Const (CF zero_big_int) (* x * 0 -> 0 *)
          | _ ->
              Binop (ty, op, e1', Const (CF c))
        else if eq_big_int c unit_big_int then
          match op with
          | Mul ->
              e1' (* x * 1 -> x *)
          | _ ->
              Binop (ty, op, e1', Const (CF c))
        else Binop (ty, op, e1', Const (CF c))
    | e1', e2' ->
        if e1' = e2' then
          match op with
          | Add ->
              Binop (ty, Mul, Const (CF (big_int_of_int 2)), e1')
              (* x + x -> 2 * x *)
          | Sub ->
              Const (CF (big_int_of_int 0)) (* x - x -> 0 *)
          | Mul ->
              Binop (ty, Mul, e1', e2')
          | _ ->
              Binop (ty, op, e1', e2')
        else Binop (ty, op, e1', e2') )
  | _ ->
      e

and calc_inputs (config : configuration) (args : expr list)
    (inputs : signal list) : configuration * expr list * signal list =
  (* iterate the args with index *)
  (* print_endline ("calc_inputs" ^ show_exprs args ); *)
  if List.length args <> List.length inputs then
    failwith "calc_inputs: args and inputs have different length" ;
  let out_args = ref [] in
  let out_inputs = ref [] in
  let out_config = ref config in
  for i = 0 to List.length args - 1 do
    let arg = List.nth args i in
    let input = List.nth inputs i in
    match snd input with
    | TBase TInt | TRef (TBase TInt, _) ->
        let i = eval_int arg config in
        out_config := (fst input, int_of_big_int i) :: !out_config
    | _ ->
        out_args := List.append !out_args [arg] ;
        out_inputs := List.append !out_inputs [input]
  done ;
  (!out_config, !out_args, !out_inputs)

and codegen_circuit (args : expr list) (g : gamma) (b : beta) (d : delta)
    (a : ralpha) (config : configuration) (c : circuit) :
    gamma * beta * ralpha * string list * expr =
  match c with
  | Circuit {name; outputs; body; _} ->
      let g', b', a', args' =
        List.fold_left
          (fun (g, b, a, args) e ->
            let g', b', a', e' = reify_expr name g b d a config e in
            (g', b', a', args @ [e']) )
          (g, b, a, []) args
      in
      (* inputs: NonDet *)
      let g1 = init_gamma c args' @ g' in
      (* let out_vars = ref [] in
         let g'', b'', a'' =
           List.fold_left
             (fun (g, b, a) (x, _) ->
               let x' = fresh_var name () in
               out_vars := !out_vars @ [x'] ;
               ((x, Var x') :: g, x' :: b, a) )
             (g1, b', a') (List.rev outputs)
         in *)
      let g''', b''', a''', final_e = reify_expr name g1 b' d a' config body in
      (g''', b''', a''', List.map (fun (x, _) -> x) outputs, final_e)
(* get name of outputs *)

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
        string_of_big_int c
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

let show_alpha (a : alpha) =
  let rec show_alpha' (a : alpha) =
    match a with
    | [] ->
        ""
    | q :: a' ->
        Format.sprintf "%s, %s" (show_alpha' a') (show_qual q)
  in
  show_alpha' a

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
      Number c
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

let rec show_config (c : configuration) : string =
  match c with
  | [] ->
      ""
  | (x, e) :: c' ->
      Format.sprintf "(%s = %s) %s" x (string_of_int e) (show_config c')

let rec parse_array (l : expr) (x : symbol) (n : int) : (symbol * symbol) list =
  match l with
  | ArrayOp (Cons, [e; xs]) ->
      let l = parse_array xs x (n + 1) in
      let l' = parse_array e (x ^ "[" ^ string_of_int n ^ "]") 0 in
      l' @ l
  | Var v ->
      (v, x) :: []
  | _ ->
      []

let rec find_in_gamma (x : symbol) (g : gamma) : (symbol * symbol) list =
  match List.assoc_opt x g with
  | Some (Var v) ->
      [(v, x)]
  | Some (ArrayOp e) ->
      parse_array (ArrayOp e) x 0
  | _ ->
      []

let humanify_arithmetic_expression (e : arithmetic_expression)
    (signals : signal list) (g : gamma) : arithmetic_expression =
  let tasks : (symbol * symbol) list =
    List.concat (List.map (fun (x, _) -> find_in_gamma x g) signals)
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

let rec get_length_from_qual (q : qual) config : int option =
  match q with
  | QTrue ->
      None
  | QNot q' ->
      get_length_from_qual q' config
  | QAnd (q1, q2) -> (
    match (get_length_from_qual q1 config, get_length_from_qual q2 config) with
    | Some _, Some _ ->
        failwith "get_length_from_qual: QAnd"
    | Some n, None ->
        Some n
    | None, Some m ->
        Some m
    | None, None ->
        None )
  | QImply (q1, q2) -> (
    match (get_length_from_qual q1 config, get_length_from_qual q2 config) with
    | Some _, Some _ ->
        failwith "get_length_from_qual: QImply"
    | Some n, None ->
        Some n
    | None, Some m ->
        Some m
    | None, None ->
        None )
  | QQuant (_, _, q') ->
      get_length_from_qual q' config
  | QExpr (Comp (Eq, e1, e2)) -> (
    match e1 with
    | ArrayOp (Length, [Var "ν"]) ->
        Some (int_of_big_int (eval_int e2 config))
    | _ ->
        None )
  | _ ->
      None

let rec type_refine (config : configuration) (t : typ) : expr =
  match t with
  | TBase _ ->
      NonDet
  | TTuple ts ->
      TMake (List.map (type_refine config) ts)
  | TRef (tarr, q) -> (
    match tarr with
    | TArr ty -> (
        let e = type_refine config ty in
        match get_length_from_qual q config with
        | Some n ->
            List.fold_left
              (fun e x -> ArrayOp (Cons, [x; e]))
              (Const CNil)
              (List.init n (fun _ -> e))
        | None ->
            failwith "type_refine: TRef" )
    | _ ->
        type_refine config tarr )
  | _ ->
      failwith "type_refine: not implemented"

let rec initial_args_list config (inputs : signal list) : expr list =
  match inputs with
  | [] ->
      []
  | (_, ty) :: inputs' ->
      type_refine config ty :: initial_args_list config inputs'

let rec type_based_output_cons (config : configuration) (s : symbol) (t : typ)
    (e : expr) : ralpha =
  match t with
  | TBase _ -> (
    match denote_expr (simplify_expr e) with
    | Some e' ->
        [RComp (REq, RVar s, e')]
    | _ ->
        raise (Failure ("type_based_output_cons: TBase" ^ show_expr e)) )
  | TTuple _ ->
      failwith "type_based_output_cons: TTuple" (* single case no tuple *)
  | TRef (tarr, q) -> (
    match tarr with
    | TArr ty -> (
      match get_length_from_qual q config with
      | Some n ->
          let out = ref [] in
          for i = 0 to n - 1 do
            let e' = get_nth_array e i in
            let s' = s ^ "[" ^ string_of_int i ^ "]" in
            out := type_based_output_cons config s' ty e' @ !out
          done ;
          !out
      | None ->
          failwith "type_refine: TRef" )
    | _ ->
        type_based_output_cons config s tarr e )
  | _ ->
      failwith "type_refine: not implemented"

let add_output_constraint (config : configuration) (a : ralpha) (e : expr)
    (out : signal list) : ralpha =
  if List.length out = 0 then a
  else if List.length out = 1 then
    type_based_output_cons config (fst (List.hd out)) (snd (List.hd out)) e @ a
  else
    match e with
    | TMake es ->
        if List.length es <> List.length out then
          failwith "output_constraint unmatched"
        else
          List.fold_left2
            (fun a e (s, t) -> type_based_output_cons config s t e @ a)
            a es out
    | _ ->
        failwith "output_constraint unmatched, not a tuple"

let buffer = ref ""

let print_to_file (filename : string) (s : string) : unit =
  let oc = open_out filename in
  Printf.fprintf oc "%s" s ; close_out oc

let print_endline_to_file (s : string) : unit =
  buffer := !buffer ^ s ;
  ()

let flush_to_file (filename : string) : unit =
  print_to_file filename !buffer ;
  buffer := "" ;
  ()

(* generate r1cs from circuit *)
let codegen (path : string) (d : delta) (config : configuration) (c : circuit) :
    unit =
  match c with
  | Circuit {name; inputs; outputs; dep; body} ->
      let inputs_without_config =
        List.filter
          (fun x -> not (List.mem (fst x) (List.map fst config)))
          inputs
      in
      let args = initial_args_list config inputs_without_config in
      let g, _, a, _, output_e =
        codegen_circuit args [] [] d [] config
          (Circuit {name; inputs= inputs_without_config; outputs; dep; body})
      in
      (* add assertion for outputs = output_e *)
      let a' = add_output_constraint config [] output_e outputs in
      let simplify_a = simplify_ralpha a @ a' in
      let transform_a = List.map transform simplify_a in
      let humanify_a =
        humanify transform_a (inputs_without_config @ outputs) g
      in
      (* print_endline
         (Format.sprintf "R1CS variables: %s" (show_ralpha simplify_a)) ; *)
      let r1cs_a = List.map r1cs_of_arithmetic_expression humanify_a in
      print_endline (Format.sprintf "=============================") ;
      print_endline
        (Format.sprintf "Circuit: %s   Config: %s   Input: %s   Output: %s" name
           (match config with [] -> "None" | _ -> show_config config)
           (show_list_signal inputs_without_config)
           (show_list_signal outputs) ) ;
      (* print_endline (Format.sprintf "variable environment: %s" (show_gamma g)) ; *)
      (* print_endline (Format.sprintf "R1CS variables: %s" (show_beta b)) ; *)
      (* print_endline (Format.sprintf "R1CS variables: %s" (show_alpha a)) ; *)
      (* print_endline (Format.sprintf "R1CS variables: %s" (show_ralpha simplify_a)) ; *)
      (* print_endline (Format.sprintf "R1CS:\n%s" (show_list_r1cs r1cs_a)) ; *)
      print_endline
        (Format.sprintf "Number of R1CS constraints: %s"
           (string_of_int (List.length r1cs_a)) ) ;
      print_endline (Format.sprintf "=============================") ;
      print_endline_to_file (show_list_r1cs r1cs_a) ;
      flush_to_file (path ^ name ^ ".r1cs") ;
      ref_counter := 0
