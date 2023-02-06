(** DSL AST *)

let nu_str = "ν"


type typ =
  (* Refinement type *)
  | TRef of refinement

    [@printer fun fmt r -> fprintf fmt "%s" (show_refinement r)]

  (* Function type: input name, input type, output type *)
  | TFun of string * typ * typ
    
    [@printer fun fmt (x, t1, t2) -> 
      match t1 with 
        | TFun _ ->  fprintf fmt "%s: (%s) -> %s" x (show_typ t1) (show_typ t2)
        | _ -> fprintf fmt "%s: %s -> %s" x (show_typ t1) (show_typ t2)]
  
  (* Array type: element type, aggregate qualifier, length expression *)
  | TArr of typ * qual * expr 
    
    [@printer fun fmt (t, q, l) -> fprintf fmt "Array<%s>[%s](%s)" (show_typ t) (show_qual q) (show_expr l)]
  
  (* Tuple type: element types *)
  | TTuple of typ list

    [@printer fun fmt (ts) -> 
      let ts_str = String.concat " × " (List.map show_typ ts) in
      fprintf fmt "%s" ts_str]
  
  (* Dependent product type: element types, and an aggregate qualifier *)
  | TDProd of typ list * string list * qual
    
    [@printer fun fmt (ts, xs, q) -> 
      let ts_str = String.concat " × " (List.map show_typ ts) in
      fprintf fmt "(%s)_(λ%s. %s)" ts_str (String.concat " " xs) (show_qual q)]
  
  [@@deriving show]

and refinement = tyBase * qual
  [@printer fun fmt (tb, q) ->
    match q with
    | QTrue -> fprintf fmt "%s" (show_tyBase tb)
    | _ -> fprintf fmt "{%s | %s}" (show_tyBase tb) (show_qual q)]
  [@@deriving show]

and tyBase = 
  | TF (* field element *) [@printer fun fmt _ -> fprintf fmt "F"]    
  | TInt (* integer *)     [@printer fun fmt _ -> fprintf fmt "Z"]    
  | TBool (* boolean *)    [@printer fun fmt _ -> fprintf fmt "B"]    
  [@@deriving show, eq] 

and ('a, 'b) binders = string list * ('a list -> 'b)
and ('a, 'b) binder = string * ('a -> 'b)

and qual =
  | QTrue                    [@printer fun fmt _ -> fprintf fmt "⊤"]
  | QExpr of expr            [@printer fun fmt e -> fprintf fmt "%s" (show_expr e)]
  | QAnd of qual * qual      [@printer fun fmt (q1,q2) -> fprintf fmt "(qand %s %s)" (show_qual q1) (show_qual q2)]
  | QImply of qual * qual    [@printer fun fmt (q1,q2) -> fprintf fmt "(qimply %s %s)" (show_qual q1) (show_qual q2)]
  | QForall of (string list) * qual [@printer fun fmt (xs,q) -> fprintf fmt "∀%s. %s" (String.concat " " xs) (show_qual q)]
  [@@deriving show]

and expr =
  | NonDet           [@printer fun fmt _ -> fprintf fmt "✧"]
  (* const *)
  | Const of const   [@printer fun fmt c -> fprintf fmt "%s" (show_const c)]
  | CPrime           [@printer fun fmt _ -> fprintf fmt "C.q"]
  | CPLen            [@printer fun fmt _ -> fprintf fmt "C.k"]
  (* variable *)
  | Var of string    [@printer fun fmt x -> fprintf fmt "%s" x]
  (* ascription *)
  | Ascribe of expr * typ  [@printer fun fmt (e,t) -> fprintf fmt "(%s :: %s)" (show_expr e) (show_typ t)]
  | AscribeUnsafe of expr * typ [@printer fun fmt (e,t) -> fprintf fmt "(%s ! <%s>)" (show_expr e) (show_typ t)]
  (* abstraction & application *)
  | LamA of string * typ * expr   [@printer fun fmt (x,t,e) -> fprintf fmt "λ%s: %s. %s" x (show_typ t) (show_expr e)]
  | Lam of string * expr   [@printer fun fmt (x,e) -> fprintf fmt "λ%s. %s" x (show_expr e)]
  | LamP of pattern * expr [@printer fun fmt (p,e) -> fprintf fmt "λ%s. %s" (show_pattern p) (show_expr e)]
  | App of expr * expr           [@printer fun fmt (e1,e2) -> fprintf fmt "%s %s" (show_expr e1) (show_expr e2)]
  (* unary operation *)
  | Opp of expr                    [@printer fun fmt e -> fprintf fmt "(- %s)" (show_expr e)]
  (* binary operation *)
  | Binop of binop_type * binop * expr * expr   [@printer fun fmt (_,op,e1,e2) -> fprintf fmt "(%s %s %s)" (show_binop op) (show_expr e1) (show_expr e2)]
  | Not of expr                    [@printer fun fmt e -> fprintf fmt "(not %s)" (show_expr e)]
  | Boolop of boolop * expr * expr [@printer fun fmt (op,e1,e2) -> fprintf fmt "(%s %s %s)" (show_boolop op) (show_expr e1) (show_expr e2)]
  | Comp of comp * expr * expr     [@printer fun fmt (op,e1,e2) -> fprintf fmt "(%s %s %s)" (show_comp op) (show_expr e1) (show_expr e2)]
  (* call: name, template *)
  | Call of string * (expr list)   [@printer fun fmt (c,args) -> fprintf fmt "#%s(%s)" c (String.concat " " (List.map show_expr args))]
  (* let-binding *)
  | LetIn of string * expr * expr  [@printer fun fmt (x,e1,e2) -> fprintf fmt "let %s = %s in %s" x (show_expr e1) (show_expr e2)]
  (* array ops *)
  | ArrayOp of (aop * expr * expr) [@printer fun fmt (op,e1,e2) -> fprintf fmt "(%s %s %s)" (show_aop op) (show_expr e1) (show_expr e2)]
  (* indexed sum: var, start, end, body *) 
  | Sum of {s: expr; e: expr; body: expr}
  (* this belongs to refinement terms *)
  | RSum of expr * expr * typ      [@printer fun fmt (s,e,t) -> fprintf fmt "\\sum_{%s, %s}(%s)" (show_expr s) (show_expr e) (show_typ t)]
  (* tuple ops *)
  | TMake of expr list [@printer fun fmt es -> fprintf fmt "(%s)" (String.concat ", " (List.map show_expr es))]
  | TGet of expr * int [@printer fun fmt (e,n) -> fprintf fmt "%s.%d" (show_expr e) n]
  (* dependent product ops *)
  | DPCons of expr list * string list * qual
  | DPDestr of expr * string list * expr
  | DPDestrP of expr * pattern * expr
  (* functional ops *)
  | Map of expr * expr
  | Zip of expr * expr
  | Foldl of {f:expr; acc:expr; xs:expr}
  | Iter of {s: expr; e: expr; body: expr; init: expr; inv: expr -> expr -> typ}
  (* Built-in functions *)
  | Fn of func * expr list [@printer fun fmt (f,es) -> fprintf fmt "(%s %s)" (show_func f) (String.concat " " (List.map show_expr es))]
  [@@deriving show]
and binop_type =
  | BNat 
  | BZ
  | BF 
and binop = 
  | Add [@printer fun fmt _ -> fprintf fmt "+"]
  | Sub [@printer fun fmt _ -> fprintf fmt "-"]
  | Mul [@printer fun fmt _ -> fprintf fmt "*"]
  | Pow [@printer fun fmt _ -> fprintf fmt "^"]
  [@@deriving show]
and boolop = 
  | And   [@printer fun fmt _ -> fprintf fmt "&&"]
  | Or    [@printer fun fmt _ -> fprintf fmt "||"]
  | Imply [@printer fun fmt _ -> fprintf fmt "==>"]
  [@@deriving show]
and aop = 
  | Cons  [@printer fun fmt _ -> fprintf fmt "cons"]
  | Get   [@printer fun fmt _ -> fprintf fmt "get"]
  | Concat [@printer fun fmt _ -> fprintf fmt "@"]
  | Scale [@printer fun fmt _ -> fprintf fmt "scale"]
  | Take [@printer fun fmt _ -> fprintf fmt "take"]
  | Drop [@printer fun fmt _ -> fprintf fmt "drop"]
  [@@deriving show]
and func = 
  | Id [@printer fun fmt _ -> fprintf fmt "id"]
  | Unint of string [@printer fun fmt s -> fprintf fmt "$%s" s]
  | ToUZ [@printer fun fmt _ -> fprintf fmt "toUZ"]
  | ToSZ [@printer fun fmt _ -> fprintf fmt "toSZ"]
  | ToBigUZ [@printer fun fmt _ -> fprintf fmt "toBigUZ"]
  | ToBigSZ [@printer fun fmt _ -> fprintf fmt "toBigSZ"]
  [@@deriving show]
and comp = 
  | Eq  [@printer fun fmt _ -> fprintf fmt "="]
  | Leq [@printer fun fmt _ -> fprintf fmt "<="]
  | Lt  [@printer fun fmt _ -> fprintf fmt "<"]
  [@@deriving show]
and const = 
  | CNil          [@printer fun fmt _ -> fprintf fmt "[]"]
  | CUnit         [@printer fun fmt _ -> fprintf fmt "()"]
  | CInt of int   [@printer fun fmt n -> fprintf fmt "%d" n]
  | CF of int     [@printer fun fmt n -> fprintf fmt "F%d" n]
  | CBool of bool [@printer fun fmt b -> fprintf fmt "%s" (Bool.to_string b)]
  [@@deriving show]
and pattern = PStr of string | PProd of pattern list [@@deriving show]

(* Statements *)
type stmt =
  | SSkip
  | SLet of string * expr
  | SLetP of pattern * expr
  | SAssert of expr * expr
  [@@deriving show]

type circuit =  Circuit of {
  name: string; 
  inputs: signal list;
  outputs: signal list;
  dep: qual option;
  body: stmt list
} [@@deriving show]

(* Circuit typing *)
and signal = string * typ [@@deriving show]
and ctyp = signal list [@printer fun fmt b -> fprintf fmt "todo"] [@@deriving show]


(* Variables *)
open Utils

module SS = StringSet

let unions ss = List.fold_left SS.union SS.empty ss
let except s x = SS.diff s (SS.singleton x)
let excepts s xs = SS.diff s (SS.of_list xs)
let count = ref 0
let fresh x = let c = !count in count := c+1; x ^ Int.to_string c

let rec vars_typ : typ -> SS.t = function
  | TRef (_, q) -> except (vars_qual q) nu_str
  | TFun (x, t1, t2) -> SS.union (vars_typ t1) (except (vars_typ t2) x)
  | TTuple _ -> todo ()
  | TDProd _ -> todo ()
  | TArr (t, q, e) -> unions [vars_typ t; except (vars_qual q) nu_str; vars_expr e]

and vars_qual : qual -> SS.t = function
  | QExpr e -> vars_expr e
  | QForall (xs, q) -> excepts (vars_qual q) xs
  | _ -> SS.empty

and vars_expr : expr -> SS.t = function
  | Const _ -> SS.empty
  | Var x -> SS.singleton x
  | Lam (x, e) -> except (vars_expr e) x
  | LamP (p, e) -> SS.diff (vars_expr e) (vars_pattern p) 
  | App (e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Opp e -> vars_expr e
  | Binop (_, _, e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Not e -> vars_expr e
  | Boolop (_, e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Comp (_, e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Call (_, es) -> unions (List.map vars_expr es)
  | ArrayOp (_, e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Sum {s=s;e=e';body=body} -> unions [vars_expr s; vars_expr e'; vars_expr body]
  | DPCons (es, xs, q) -> todos "vars_expr: DPCons"
  | TMake es -> unions (List.map vars_expr es)
  | DPDestr (e1, xs, e2) -> SS.union (vars_expr e1) (excepts (vars_expr e2) xs)
  | DPDestrP (e1, p, e2) -> SS.union (vars_expr e1) (SS.diff (vars_expr e2) (vars_pattern p))
  | Map (e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Zip (e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Foldl {f; acc; xs} -> unions (List.map vars_expr [f; acc; xs])
  | Iter {s; e; body; init; inv} ->
    let vars_e = unions (List.map vars_expr [s;e;body;init]) in
    let (x1, x2) = (fresh "_var", fresh "_var") in
    let vars_inv = excepts (vars_typ (inv (Var x1) (Var x2))) [x1; x2] in
    unions [vars_e; vars_inv]
  | Fn (_, es) -> unions (List.map vars_expr es)
  
and vars_pattern : pattern -> SS.t = function
  | PStr x -> SS.singleton x
  | PProd pp -> unions (List.map vars_pattern pp)

let rec subst_typ (x: string) (e: expr) (t: typ) : typ =
  let f = subst_typ x e in
  match t with
  | TRef (tb, q) -> TRef (tb, subst_qual x e q)
  | TFun (y, t1, t2) ->
    if x = y then
      t
    else
      (* TODO: alpha-rename *)
      TFun (y, subst_typ x e t1, subst_typ x e t2) 
  | TArr (t, q, e') -> TArr (f t, subst_qual x e q, subst_expr x e e')
  | TTuple ts -> TTuple (List.map f ts)
  | TDProd (ts, ys, q) ->
    let ts' = List.map f ts in
    if List.exists ((=)x) ys then
      TDProd (ts', ys, q)
    else
      TDProd (ts', ys, subst_qual x e q)

and subst_qual (x: string) (e: expr) (q: qual) : qual =
  match q with
  | QTrue -> q
  | QAnd (q1, q2) -> QAnd (subst_qual x e q1, subst_qual x e q2)
  | QExpr e' -> QExpr (subst_expr x e e')
  | QForall (ys, q') ->
    match (List.find_opt (fun y -> x = y) ys) with
    | Some _ -> q
    | None -> QForall (ys, subst_qual x e q')

and subst_expr (x: string) (ef: expr) (e: expr) : expr =
  let f = subst_expr x ef in
  match e with
  | Const _ -> e
  | CPrime -> e
  | CPLen -> e
  | Var y -> if x = y then ef else e
  | LamA (y, t, body) ->
    if x = y then e else LamA (y, subst_typ x ef t, f body)
  | App (e1, e2) -> App (f e1, f e2)
  | Not e' -> Not (f e')
  | Opp e' -> Opp (f e')
  | Binop (t, op, e1, e2) -> Binop (t, op, f e1, f e2)
  | Boolop (op, e1, e2) -> Boolop (op, f e1, f e2)
  | Comp (op, e1, e2) -> Comp (op, f e1, f e2) 
  | Call (c, es) -> Call (c, List.map f es)
  | ArrayOp (op, e1, e2) -> ArrayOp (op, f e1, f e2)
  | TMake es -> TMake (List.map f es)
  | TGet (e, n) -> TGet (f e, n)
  | Fn (fn, es) -> Fn (fn, List.map f es)
  | Iter {s; e; body; init; inv} ->
    Iter {
      s = f s; 
      e = f e; 
      body = f body; 
      init = f init; 
      inv = (fun ei -> fun ex -> (subst_typ x ef (inv ei ex)))
    }
  | Sum {s=s;e=e';body=body} -> Sum {s=f s; e=f e'; body=f body}
  | RSum (s,e,t) -> RSum (f s, f e, subst_typ x ef t)
  | DPCons (es, ys, q) ->
    let es' = List.map f es in
    if List.exists ((=)x) ys then
      DPCons (es', ys, q)
    else
      DPCons (es', ys, subst_qual x ef q)
  | DPDestr (e1, ys, e2) -> 
    if List.exists ((=)x) ys then
      DPDestr (f e1, ys, e2)
    else
      DPDestr (f e1, ys, f e2)
  | DPDestrP (e1, p, e2) -> todos "subst_expr: DPDestrP"
  | Map (e1, e2) -> todos "subst_expr: Map"
  | Zip (e1, e2) -> todos "subst_expr: Zip"
  | Foldl {f; acc; xs} -> todos "subst_expr: Foldl"
  | _ -> todos "subst_expr"
  