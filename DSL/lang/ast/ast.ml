(** DSL abstract syntax tree *)

(* Constrainable expressions *)
type expr =
  | Sig of int
  | Var of string
  | Opp of expr
  | Add of expr * expr
  | Mul of expr * expr

(* Statements *)
type stmt =
  (* Constraint *)
  | Con of expr * expr

type stmts = stmt list
