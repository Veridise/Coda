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

(* Statements *)
type stmt =
  (* Constraint *)
  | Constraint of expr * expr
  (* Map *)
  | Map of (string * varDecl) * stmt list * expr

type stmts = stmt list

(* Circuit *)
type circuit = 
  | Template of string * (string * varDecl) list * stmts

(* Program *)
type program = circuit list

(* Environment: for typechecking *)
type env = string -> ((string * varDecl) list) option

val genv: program -> env
val is_zero: circuit
val is_equal: circuit
val num2bits_32: circuit
