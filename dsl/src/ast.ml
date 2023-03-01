(** DSL AST *)

let nu_str = "ν"


type tyBase = 
  | TF (* field element *)
  | TInt (* integer *)    
  | TBool (* boolean *)   
  [@@deriving eq] 


type typ =
  (* Refinement type: (base type, qualifier) *)
  | TRef of tyBase * qual
  (* Function type: (input name, input type, output type) *)
  | TFun of string * typ * typ
  (* Array type: (element type, aggregate qualifier, length expression) *)
  | TArr of typ * qual * expr
  (* Tuple type: [element type] *)
  | TTuple of typ list
  (* Dependent product type: ([element type], aggregate qualifier) *)
  | TDProd of typ list * string list * qual

and qual =
  | QTrue                    
  | QExpr of expr        
  | QNot of qual    
  | QAnd of qual * qual      
  | QImply of qual * qual
  | QForall of (string * expr * expr) * qual 

and expr =
  | NonDet           
  (* const *)
  | Const of const   
  | CPrime           
  | CPLen            
  (* variable *)
  | Var of string    
  (* ascription *)
  | Ascribe of expr * typ  
  | AscribeUnsafe of expr * typ 
  (* abstraction & application *)
  | LamA of string * typ * expr   
  | Lam of string * expr
  | LamP of pattern * expr
  | App of expr * expr           
  (* binary operation *)
  | Binop of binop_type * binop * expr * expr
  | Not of expr                    
  | Boolop of boolop * expr * expr 
  | Comp of comp * expr * expr     
  (* call: name, template *)
  | Call of string * (expr list)   
  (* let-binding *)
  | LetIn of string * expr * expr
  (* array ops *)
  | ArrayOp of (aop * expr list) 
  (* indexed sum: var, start, end, body *) 
  | Sum of {s: expr; e: expr; body: expr}
  (* this should belong to refinement terms *)
  | RSum of expr * expr * typ      
  (* tuple ops *)
  | TMake of expr list 
  | TGet of expr * int 
  (* dependent product ops *)
  | DPCons of expr list * string list * qual
  | DPDestr of expr * string list * expr
  | DPDestrP of expr * pattern * expr
  (* functional ops *)
  | Map of expr * expr
  | Foldl of {f:expr; acc:expr; xs:expr}
  | Iter of {s: expr; e: expr; body: expr; init: expr; inv: expr -> expr -> typ}
  (* Built-in functions *)
  | Fn of func * expr list 
and binop_type =
  | BNat 
  | BZ
  | BF 
and binop = 
  | Add 
  | Sub 
  | Mul 
  | Pow 
and boolop = 
  | And   
  | Or    
  | Imply 
and aop = 
  | Cons  
  | Get   
  | Concat 
  | Scale 
  | Take 
  | Drop 
  | Zip
and func = 
  | Id 
  | Unint of string 
  | ToUZ 
  | ToSZ 
  | ToBigUZ 
  | ToBigSZ 
and comp = 
  | Eq  
  | Leq 
  | Lt  
and const = 
  | CNil
  | CUnit         
  | CInt of int   
  | CF of int     
  | CBool of bool 
and pattern = PStr of string | PProd of pattern list

(* Statements *)
type stmt =
  | SSkip
  | SLet of string * expr
  | SLetP of pattern * expr
  | SAssert of expr * expr

type signal = string * typ
type circuit =  Circuit of {
  name: string; 
  inputs: signal list;
  outputs: signal list;
  dep: qual option;
  body: stmt list
}
