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

(* generate environment from program *)
let genv (p: program) : env =
  let rec genv' (p: program) (e: env) : env =
    match p with
    | [] -> e
    | (Template (name, args, _))::p' -> 
        genv' p' (fun x -> if x = name then Some args else e x)
  in genv' p (fun _ -> None)

(* Examples *)
let is_zero = 
  Template ("IsZero", 
            [("in", Input Expr);
             ("out", Output Expr);
             ("inv", Input Expr)], 
            [Constraint (Var "out", Add (Opp (Mul (Var "in", Var "inv")), Sig 1));
             Constraint (Mul (Var "in", Var "out"), Sig 0)])

let is_equal =
  Template ("IsEqual", 
            [("in", Input (Array [2]));
             ("out", Output Expr);
             ("isz", Input Expr)],
            [Constraint (Var "isz", Call "IsZero");
             Constraint (Sub (Get (Var "in", 1), Get (Var "in", 0)), Field (Var "isz", "in"));
             Constraint (Var "out", Field (Var "isz", "out"))])

let num2bits_32 =
  Template ("Num2Bits_32",
            [("in", Input Expr);
             ("out", Output (Array [4]));
             ("lc1", Signal Expr)],
            [Map (("s", Signal Expr),
                  [Constraint (Mul (Var "s", Sub (Var "s", Sig 1)), Sig 0)],
                  Var "out");
             Constraint (Var "lc1", Var "in")])
