(** DSL AST *)

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
  | TArr of typ * qual * expr 
    
    [@printer fun fmt (t, q, l) -> fprintf fmt "Array<%s>[%s](%s)" (show_typ t) (show_qual q) (show_expr l)]
  
  (* Product type: element types, optional aggregate qualifier *)
  | TProd of typ list * (string list * qual) option
    
    [@printer fun fmt (ts, q) -> let ts_str = String.concat " × " (List.map show_typ ts) in
      match q with
      | None -> fprintf fmt "%s" ts_str
      | Some (xs, q) -> fprintf fmt "(%s)_(λ%s. %s)" ts_str (String.concat " " xs) (show_qual q)]
  
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

and qual =
  | QP (* field size *)      [@printer fun fmt _ -> fprintf fmt "p"]
  | QExpr of expr            [@printer fun fmt e -> fprintf fmt "<expr>"]
  | QTrue                    [@printer fun fmt _ -> fprintf fmt "⊤"]
  | QForall of string * qual [@printer fun fmt (s,q) -> fprintf fmt "∀%s. %s" s (show_qual q)]
  [@@deriving show]

and expr =
  (* const *)
  | Const of const   [@printer fun fmt c -> fprintf fmt "%s" (show_const c)]    
  (* variable *)
  | Var of string    [@printer fun fmt x -> fprintf fmt "%s" x]
  (* abstraction *)
  | Lam of string * typ * expr   [@printer fun fmt (x,tx,e) -> fprintf fmt "λ%s: %s. %s" x (show_typ tx) (show_expr e)]
  | LamP of pattern * typ * expr [@printer fun fmt (p,tx,e) -> fprintf fmt "λ%s: %s. %s" (show_pattern p) (show_typ tx) (show_expr e)]
  (* application *)
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
  | LetIn of string * typ option * expr * expr
  (* array ops *)
  | ArrayOp of (aop * expr * expr) [@printer fun fmt (op,e1,e2) -> fprintf fmt "(%s %s %s)" (show_aop op) (show_expr e1) (show_expr e2)]
  (* indexed sum: var, start, end, body *) 
  | Sum of string * expr * expr * expr [@printer fun fmt (i,s,e,b) -> fprintf fmt "sum_{%s <= %s <= %s} %s" (show_expr s) i (show_expr e) (show_expr b)]
  (* product ops *)
  | PCons of expr list * (string list * qual) option
  | PDestr of expr * string list * expr
  | PDestrP of expr * pattern * expr
  (* functional ops *)
  | Map of expr * expr
  | Zip of expr * expr
  | Foldl of {f:expr; acc:expr; xs:expr}
  | Iter of {s: expr; e: expr; body: expr; init: expr; inv: expr -> expr -> qual}
  | Fn of func * expr
  [@@deriving show]
and binop = Add | Sub | Mul | Pow [@@deriving show]
and boolop = And | Or | Imply [@@deriving show]
and aop = Cons | Get | Scale | Take | Drop [@@deriving show]
and func = Id | ToUZ | ToSZ [@@deriving show]
and comp = Eq | Leq | Lt [@@deriving show]
and const = CNil | CUnit | CInt of int | CF of int | CBool of bool [@@deriving show]
and pattern = PStr of string | PProd of pattern list [@@deriving show]

(* Statements *)
type stmt =
  | SSkip
  | SLet of string * typ option * expr
  | SLetP of pattern * typ option * expr
  | SAssert of expr
  | SForall of (string list -> expr)
  [@@deriving show]

type circuit =  Circuit of {
  name: string; 
  signals: signal list;
  property: qual option;
  body: stmt list
} [@@deriving show]

(* Circuit typing *)
and signal = string * mode * typ [@@deriving show]
and ctyp = signal list * qual option [@@deriving show]
and mode = Input | Output | Exists [@@deriving show]


(* Variables *)
open Utils

module SS = StringSet

let unions ss = List.fold_left SS.union SS.empty ss
let except s x = SS.diff s (SS.singleton x)
let excepts s xs = SS.diff s (SS.of_list xs)
let nu_str = "ν"
let count = ref 0
let fresh () = let c = !count in count := c+1; "_var_" ^ Int.to_string c

let rec vars_typ : typ -> SS.t = function
  | TRef (_, q) -> except (vars_qual q) nu_str
  | TFun (x, tx, tr) -> SS.union (vars_typ tx) (except (vars_typ tr) nu_str)
  | TProd _ -> todo ()
  | TArr (t, q, e) -> unions [vars_typ t; except (vars_qual q) nu_str; vars_expr e]

and vars_qual : qual -> SS.t = function
  | QExpr e -> vars_expr e
  | QForall (x, q) -> except (vars_qual q) x
  | _ -> SS.empty

and vars_expr : expr -> SS.t = function
  | Const _ -> SS.empty
  | Var x -> SS.singleton x
  | Lam (x, _, e) -> except (vars_expr e) x
  | LamP (p, _, e) -> SS.diff (vars_expr e) (vars_pattern p) 
  | App (e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Opp e -> vars_expr e
  | Binop (_, e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Not e -> vars_expr e
  | Boolop (_, e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Comp (_, e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Call (_, es) -> unions (List.map vars_expr es)
  | ArrayOp (_, e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Sum (i, s, e, b) -> unions [vars_expr s; vars_expr e; except (vars_expr b) i]
  | PCons (es, Some (xs, q)) -> unions ((excepts (vars_qual q) xs) :: (List.map vars_expr es))
  | PDestr (e1, xs, e2) -> SS.union (vars_expr e1) (excepts (vars_expr e2) xs)
  | PDestrP (e1, p, e2) -> SS.union (vars_expr e1) (SS.diff (vars_expr e2) (vars_pattern p))
  | Map (e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Zip (e1, e2) -> SS.union (vars_expr e1) (vars_expr e2)
  | Foldl {f; acc; xs} -> unions (List.map vars_expr [f; acc; xs])
  | Iter {s; e; body; init; inv} ->
    let vars_e = unions (List.map vars_expr [s;e;body;init]) in
    let (x1, x2) = (fresh (), fresh ()) in
    let vars_inv = excepts (vars_qual (inv (Var x1) (Var x2))) [x1; x2] in
    unions [vars_e; vars_inv]
  | Fn (_, e) -> vars_expr e
  
and vars_pattern : pattern -> SS.t = function
  | PStr x -> SS.singleton x
  | PProd pp -> unions (List.map vars_pattern pp)
