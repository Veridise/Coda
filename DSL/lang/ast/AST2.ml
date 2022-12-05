(** DSL AST *)

(* expression typing *)
type typ =
  | TRef of refinement
  | TFun of string * refinement * typ
  | TProd of typ list * qual option
  | TArr of typ * qual * expr
  [@@deriving show, eq]

and refinement = tyBase * qual

and tyBase = 
  | TF (* field element *)
  | TInt (* integer *)
  | TBool (* boolean *)
  [@@deriving show, eq]

and qual =
  | QP (* field size *)
  | QToZ of expr (* unsigned conversion *)
  | QToZS of expr (* signed conversion *)
  | QAsZ of expr (* unsigned big int *)
  | QAsZS of expr (* signed big int *)
  | QExpr of expr
  | QTrue
  | QIte of qual * qual * qual
  | QForall of string * qual
  [@@deriving show, eq]

and expr =
  (* const *)
  | Const of const
  (* variable *)
  | Var of string
  (* abstraction *)
  | Lam of pattern * typ * expr
  (* application *)
  | App of expr * expr
  (* unary operation *)
  | Opp of expr
  | Not of expr
  (* binary operation *)
  | Binop of binop * expr * expr
  | Boolop of boolop * expr * expr
  (* equality *)
  | Eq of expr * expr
  (* call: name, template *)
  | Call of string * (expr list)
  (* let-binding *)
  | LetIn of string * typ option * expr * expr
  (* array ops *)
  | Cons of expr * expr
  | Get of expr * expr
  | Scale of expr * expr
  | Take of expr
  | Drop of expr
  (* indexed sum: var, start, end, body *)
  | Sum of string * expr * expr * expr
  (* product ops *)
  | PCons of expr list * qual option
  | PDestr of expr * pattern * expr
  (* functional ops *)
  | Map of expr * expr
  | Zip of expr * expr
  | Foldl of {f:expr; acc:expr; xs:expr}
  [@@deriving show, eq]
and binop = Add | Sub | Mul | Pow
and boolop = And | Or
  [@@deriving show, eq]
and const = CNil | CUnit | CInt of int | CF of int | CBool of bool
  [@@deriving show, eq]
and pattern = PStr of string | PProd of pattern list

(* Statements *)
type stmt =
  | SSkip
  | SLet of string * typ option * expr
  | SLetP of pattern * typ option * expr
  | SAssert of expr
  [@@deriving show, eq]

type circuit = 
  Circuit of {name:string; params: ctyp; body: stmt list}
  [@@deriving show, eq]

(* Circuit typing *)
and ctyp = (string * mode * typ) list [@@deriving show, eq]

and mode = Input | Output | Exists [@@deriving show, eq]

(* circuit declarations *)
type delta = (string * ctyp) list [@@deriving show, eq]
(* typing environment *)
type gamma = (string * typ) list [@@deriving show, eq]
 
let tf = TRef (TF, QTrue)
let tint = TRef (TInt, QTrue)
let tbool = TRef (TBool, QTrue)
let opp e = Opp e
let add e1 e2 = Binop (Add, e1, e2)
let sub e1 e2 = Binop (Sub, e1, e2)
let mul e1 e2 = Binop (Mul, e1, e2)
let pow e1 e2 = Binop (Pow, e1, e2)
let eq e1 e2 = Eq (e1, e2)
let bor e1 e2 = Boolop (Or, e1, e2)
let band e1 e2 = Boolop (And, e1, e2)
let assert_eq e1 e2 = SAssert (eq e1 e2)
let v x = Var x
let nu = Var "nu"
let fc n = Const (CF n)
let zc n = Const (CInt n)
let f0 = fc 0
let f1 = fc 1
let f2 = fc 2
let z0 = zc 0
let z1 = zc 1
let z2 = zc 2
let tf_binary = TRef (TF, QExpr (bor (eq nu f0) (eq nu f1)))
let slet x e = SLet (x, None, e)
let sum si es ee eb = Sum (si, es, ee, eb)
let get xs i = Get (xs, i)
let toBigInt (i: string) (n: expr) (k: expr) (xs: expr) : expr = 
  let ei = v i in
  sum i z0 k (mul (get xs ei) (pow f2 (mul n ei)))

let is_zero_spec = TRef (TF, QIte (QExpr (eq (v "in") f0), QExpr (eq nu f1), QExpr (eq nu f0)))
let is_zero = Circuit {
  name = "isZero";
  params = [("in", Input, tf); ("out", Output, is_zero_spec); ("inv", Exists, tf)];
  body = [
    assert_eq (v "out") (add (opp (mul (v "in") (v "inv"))) f1);
    assert_eq (mul (v "in") (v "out")) f0
  ]
}

let is_equal_spec = TRef (TF, QIte (QExpr (eq (v "x") (v "y")), QExpr (eq nu f1), QExpr (eq nu f0)))
let is_equal = Circuit {
  name = "isEqual";
  params = [("x", Input, tf); ("y", Input, tf); ("out", Output, is_equal_spec)];
  body = [
    slet "z0" (Call ("isZero", [sub (v "x") (v "y")]));
    slet "z1" (sub f1 (v "z0"));
    assert_eq (v "out") (v "z1")
  ]
}



let num2bits = Circuit {
  name = "Num2Bits";
  params = [
    ("n", Input, tint); 
    ("in", Input, tf); 
    ("out", Output, TArr (tf_binary, QExpr (eq (toBigInt "i" z1 (v "n") nu) (v "in")), v "n"))
  ];
  body = [
    SSkip;
    ]
    (* SLetP (PProd [PStr "_", PStr "lc1", PStr "_", PStr "cons"]) (Foldl {
      f=Lam (PProd [PProd [PStr "i", PStr "lc1", PStr "e2", PStr "cons"]; PStr "outi"],
          PCons ([
            (* i *)
            add (v "i") z1;
            (* lc1 *)
            add (v "lc1") (mul (v "outi") (v "e2"));
            (* e2 *)
            add (v "e2") (v "e2");
            (* cons *)
            band cons (eq f0 (mul (v "outi") (sub (v "outi") f1)))
          ], None));
      acc=PCons ([f0, f0, f1, CBool true]);
      xs=(v "out")});
    SAssert (and (v "cons", eq (v "lc1") (v "in"))) *)
  
}

type alpha = expr list

let d_empty = []

let g_empty = []

let a_empty = []

let add_to_delta (d: delta) (c: circuit) : delta =
  match c with
  | Circuit {name;params;body} -> (name, params) :: d

let d = add_to_delta d_empty is_zero

let todo () = failwith "not implemented"
let todos s = failwith (s ^ ": not implemented")

type cons = Subtype of gamma * alpha * typ * typ | HasType of gamma * alpha * string * typ

let functionalize (ctype: ctyp) : typ list * typ =
  let get_typ (_,_,t) = t in
  let inputs = List.filter (function (_,Input,_) -> true | _ -> false) ctype in
  let outputs = List.filter (function (_,Output,_) -> true | _ -> false) ctype in 
  assert (List.length outputs = 1);
  (List.map get_typ inputs, get_typ (List.hd outputs))

let typecheck (d: delta) (g: gamma) (a: alpha) (e: expr) : (typ * cons list) = 
  let rec f : expr -> typ * cons list = function
    | Const c -> 
      let t = match c with
        | CF _ -> TRef (TF, QExpr (Eq (v "nu", e)))
        | _ -> failwith "Non-field constant"
      in (t, [])
    | Var v ->
      let t = match List.assoc_opt v g with
        | Some t -> t
        | None -> failwith ("No such variable: " ^ v) in
      (t, [])
    | Binop (op, e1, e2) ->
      (* TODO: reflect *)
      let (t1, cs1) = f e1 in
      let (t2, cs2) = f e2 in
      (TRef (TF, QExpr (Eq (Var "nu", (Binop (op, e1, e2))))), cs1 @ cs2)
    | Opp e ->
      (* TODO: reflect *)
      f e
    | Call (circ, args) ->
      (match List.assoc_opt circ d with
      | Some ctype -> 
        let (args_t, args_cs) = List.map f args |> List.split  in
        let (params_t, out_t) = functionalize ctype in
        let subs = List.map (fun (arg_t, param_t) -> Subtype (g, a, arg_t, param_t)) (List.combine args_t params_t) in
        (out_t, List.concat args_cs @ subs)
      | None -> failwith ("No such circuit: " ^ circ))
    | Eq (e1, e2) ->
      let (t1, cs1) = f e1 in
      let (t2, cs2) = f e2 in
      (tbool, cs1 @ cs2)
    | _ -> todo ()
  in f e

let typecheck_stmt (d: delta) (g: gamma) (a: alpha) (s: stmt) : (gamma * alpha * cons list) =
  match s with
  | SSkip -> (g, [], [])
  | SLet(x, t, e) ->
    (* TODO: assert t' :< t *)
    let (t', cs) = typecheck d g a e in
    ((x,t')::g, [], cs)
  | SAssert e ->
    (g, [e], [])

let rec to_base_typ = function
  | TRef (tb, _) -> TRef (tb, QTrue)
  | TArr (t,_,n) -> TArr (to_base_typ t, QTrue, n)
  | TFun _ -> todos "to_base_typ: TFun"
  | TProd _ -> todos "to_base_typ: TProd"
  [@@deriving show, eq]
  
let init_gamma (c: circuit) : gamma =
  match c with
  | Circuit {name;params;body} ->
    List.map (function
      (* populate gamma with pre-conditions *)
      | (x,Input,t) -> (x, t) 
      (* ignore post-conditions *)
      | (x,Output,t) -> (x, to_base_typ t)
      (* ignore existential variables *)
      | (x,Exists,t) -> (x, to_base_typ t)) params
  
let typecheck_circuit (d: delta) (c: circuit) : cons list =
  match c with
  | Circuit {name;params;body} ->
    let (g, a, cs) = List.fold_left
      (fun ((g, a, cs): gamma * alpha * cons list) (s: stmt) ->
        let (g', a', cs') = typecheck_stmt d g a s in 
        (g', a @ a', cs @ cs'))
      (init_gamma c, [], [])
      body in
    let outputs = List.filter (function (_,Output,_) -> true | _ -> false) params in
    let out_cons = List.map (fun (x,_,t) -> HasType (g, a, x, t)) outputs in
    cs @ out_cons