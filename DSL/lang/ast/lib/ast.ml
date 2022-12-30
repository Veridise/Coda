(** DSL AST *)

let nu_str = "ν"

type typ =
  (* Refinement type *)
  | TRef of refinement

    [@printer fun fmt r -> fprintf fmt "%s" (show_refinement r)]

  (* Function type: input name, input type, output type *)
  | TFun of (string * typ * typ)
    
    [@printer fun fmt (x, tx, tr) -> 
      match tx with 
        | TFun _ ->  fprintf fmt "%s: (%s) -> %s" x (show_typ tx) (show_typ tr)
        | _ -> fprintf fmt "%s: %s -> %s" x (show_typ tx) (show_typ tr)]
  
  (* Array type: element type, aggregate qualifier, length expression *)
  | TArr of typ * (expr -> qual) * expr 
    
    [@printer fun fmt (t, q, l) -> fprintf fmt "Array<%s>[%s](%s)" (show_typ t) (show_qual (q (Var nu_str))) (show_expr l)]
  
  (* Tuple type: element types *)
  | TTuple of typ list

    [@printer fun fmt (ts) -> 
      let ts_str = String.concat " × " (List.map show_typ ts) in
      fprintf fmt "%s" ts_str]
  
  (* Dependent product type: element types, and an aggregate qualifier *)
  | TDProd of typ list * ((expr, qual) binder)
    
    (* [@printer fun fmt (ts, (xs, q)) -> 
      let ts_str = String.concat " × " (List.map show_typ ts) in
      fprintf fmt "(%s)_(λ%s. %s)" ts_str (String.concat " " xs) (show_qual (q (List.map (fun x -> Var x) xs)))] *)
  
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

and ('a, 'b) binder = string list * ('a list -> 'b)

and qual =
  | QP (* field size *)      [@printer fun fmt _ -> fprintf fmt "p"]
  | QExpr of expr            [@printer fun fmt e -> fprintf fmt "%s" (show_expr e)]
  | QTrue                    [@printer fun fmt _ -> fprintf fmt "⊤"]
  | QForall of string * qual [@printer fun fmt (s,q) -> fprintf fmt "∀%s. %s" s (show_qual q)]
  [@@deriving show]

and expr =
  (* const *)
  | Const of const   [@printer fun fmt c -> fprintf fmt "%s" (show_const c)]    
  (* variable *)
  | Var of string    [@printer fun fmt x -> fprintf fmt "%s" x]
  (* ascription *)
  | Ascribe of expr * typ  [@printer fun fmt (e,t) -> fprintf fmt "(%s :: %s)" (show_expr e) (show_typ t)]
  (* abstraction & application *)
  | LamA of string * typ * expr   [@printer fun fmt (x,t,e) -> fprintf fmt "λ%s: %s. %s" x (show_typ t) (show_expr e)]
  | Lam of string * expr   [@printer fun fmt (x,e) -> fprintf fmt "λ%s. %s" x (show_expr e)]
  | LamP of pattern * expr [@printer fun fmt (p,e) -> fprintf fmt "λ%s. %s" (show_pattern p) (show_expr e)]
  | App of expr * expr           [@printer fun fmt (e1,e2) -> fprintf fmt "%s %s" (show_expr e1) (show_expr e2)]
  (* unary operation *)
  | Opp of expr                    [@printer fun fmt e -> fprintf fmt "(- %s)" (show_expr e)]
  (* binary operation *)
  | Binop of binop * expr * expr   [@printer fun fmt (op,e1,e2) -> fprintf fmt "(%s %s %s)" (show_binop op) (show_expr e1) (show_expr e2)]
  | Not of expr                    [@printer fun fmt e -> fprintf fmt "(not %s)" (show_expr e)]
  | Boolop of boolop * expr * expr [@printer fun fmt (op,e1,e2) -> fprintf fmt "(%s %s %s)" (show_boolop op) (show_expr e1) (show_expr e2)]
  | Comp of comp * expr * expr     [@printer fun fmt (op,e1,e2) -> fprintf fmt "(%s %s %s)" (show_comp op) (show_expr e1) (show_expr e2)]
  (* call: name, template *)
  | Call of string * (expr list)   [@printer fun fmt (c,args) -> fprintf fmt "#%s(%s)" c (String.concat " " (List.map show_expr args))]
  (* let-binding *)
  | LetIn of string * expr * expr
  (* array ops *)
  | ArrayOp of (aop * expr * expr) [@printer fun fmt (op,e1,e2) -> fprintf fmt "(%s %s %s)" (show_aop op) (show_expr e1) (show_expr e2)]
  (* indexed sum: var, start, end, body *) 
  | Sum of string * expr * expr * expr [@printer fun fmt (i,s,e,b) -> fprintf fmt "sum_{%s <= %s <= %s} %s" (show_expr s) i (show_expr e) (show_expr b)]
  (* tuple ops *)
  | TMake of expr list [@printer fun fmt es -> fprintf fmt "(%s)" (String.concat ", " (List.map show_expr es))]
  | TGet of expr * int [@printer fun fmt (e,n) -> fprintf fmt "%s.%d" (show_expr e) n]
  (* dependent product ops *)
  | DPCons of expr list * ((expr, qual) binder)
  | DPDestr of expr * string list * expr
  | DPDestrP of expr * pattern * expr
  (* functional ops *)
  | Map of expr * expr
  | Zip of expr * expr
  | Foldl of {f:expr; acc:expr; xs:expr}
  | Iter of {s: expr; e: expr; body: expr; init: expr; inv: expr -> expr -> typ}
  (* Built-in functions *)
  | Fn of func * expr [@printer fun fmt (f,e) -> fprintf fmt "(%s %s)" (show_func f) (show_expr e)]
  [@@deriving show]
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
and aop = Cons | Get | Scale | Take | Drop [@@deriving show]
and func = 
  | Id [@printer fun fmt _ -> fprintf fmt "id"]
  | ToUZ [@printer fun fmt _ -> fprintf fmt "toUZ"]
  | ToSZ [@printer fun fmt _ -> fprintf fmt "toSZ"]
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
  | SAssert of expr
  | SForall of (string list -> expr)
  [@@deriving show]

type circuit =  Circuit of {
  name: string; 
  inputs: signal list;
  exists: signal list;
  outputs: signal list;
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
let fresh () = let c = !count in count := c+1; "_var_" ^ Int.to_string c

let rec vars_typ : typ -> SS.t = function
  | TRef (_, q) -> except (vars_qual q) nu_str
  | TFun (x, tx, tr) -> SS.union (vars_typ tx) (except (vars_typ tr) nu_str)
  | TTuple _ -> todo ()
  | TDProd _ -> todo ()
  | TArr (t, q, e) -> unions [vars_typ t; except (vars_qual (q (Var nu_str))) nu_str; vars_expr e]

and vars_qual : qual -> SS.t = function
  | QExpr e -> vars_expr e
  | QForall (x, q) -> except (vars_qual q) x
  | _ -> SS.empty

and vars_expr : expr -> SS.t = function
  | Const _ -> SS.empty
  | Var x -> SS.singleton x
  | Lam (x, e) -> except (vars_expr e) x
  | LamP (p, e) -> SS.diff (vars_expr e) (vars_pattern p) 
  | App (e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Opp e -> vars_expr e
  | Binop (_, e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Not e -> vars_expr e
  | Boolop (_, e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Comp (_, e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Call (_, es) -> unions (List.map vars_expr es)
  | ArrayOp (_, e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Sum (i, s, e, b) -> unions [vars_expr s; vars_expr e; except (vars_expr b) i]
  | DPCons (es, (xs, q)) ->
      let q' = q (List.map (fun x -> Var x) xs) in
      unions ((excepts (vars_qual q') xs) :: (List.map vars_expr es))
  | TMake es -> unions (List.map vars_expr es)
  | DPDestr (e1, xs, e2) -> SS.union (vars_expr e1) (excepts (vars_expr e2) xs)
  | DPDestrP (e1, p, e2) -> SS.union (vars_expr e1) (SS.diff (vars_expr e2) (vars_pattern p))
  | Map (e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Zip (e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Foldl {f; acc; xs} -> unions (List.map vars_expr [f; acc; xs])
  | Iter {s; e; body; init; inv} ->
    let vars_e = unions (List.map vars_expr [s;e;body;init]) in
    let (x1, x2) = (fresh (), fresh ()) in
    let vars_inv = excepts (vars_typ (inv (Var x1) (Var x2))) [x1; x2] in
    unions [vars_e; vars_inv]
  | Fn (_, e) -> vars_expr e
  
and vars_pattern : pattern -> SS.t = function
  | PStr x -> SS.singleton x
  | PProd pp -> unions (List.map vars_pattern pp)
