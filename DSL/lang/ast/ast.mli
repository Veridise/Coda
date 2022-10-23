(** DSL AST *)

(* Constrainable expressions *)
type expr =
  (* const *)
  | Sig of int
  (* variable *)
  | Var of string
  (* array operation *)
  | Get of expr * int
  (* unary operation *)
  | Opp of expr
  (* binary operation *)
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  (* call template *)
  | Call of string
  (* template field *)
  | Field of expr * string

(* Signal array *)
type varType = 
  | Array of int list (* var x[123][456][789]] ==> Array [123;456;789] *)
  | Expr (* var x; *)

(* Circuit inputs and outputs / temp vars *)
type varDecl =
  | Input of varType
  | Output of varType
  | Signal of varType

type var = string * varDecl

(* Statements *)
type stmt =
  (* Constraint *)
  | Constraint of expr * expr
  (* Map (fun a -> stmts) arr *)
  | Map of var * stmt list * expr
  (* Map2 (fun a b -> stmts) arr_a arr_b *)
  | Map2 of var * var * stmt list * expr * expr
  (* Foldl (fun acc a -> stmts) acc arr *)
  | Foldl of var * var * stmt list * expr * expr
  (* Foldl2 (fun acc a b -> stmts) acc arr_a arr_b *)
  | Foldl2 of var * var * var * stmt list * expr * expr * expr
  (* Foldr (fun a acc -> stmts) arr acc *)
  | Foldr of var * var * stmt list * expr * expr
  (* Foldr2 (fun a b acc -> stmts) arr_a arr_b acc *)
  | Foldr2 of var * var * var * stmt list * expr * expr * expr

type stmts = stmt list

(* Circuit *)
type circuit = 
  | Template of string * var list * stmts

(* Program *)
type program = circuit list

(* Environment: for typechecking *)
type env = string -> (var list) option

val genv: program -> env
val is_zero: circuit
val is_equal: circuit
val num2bits_32: circuit
