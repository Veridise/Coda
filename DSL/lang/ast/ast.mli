type expr =
  | Sig of int
  | Var of string
  | Opp of expr
  | Add of expr * expr
  | Mul of expr * expr

type stmt =
  | Con of expr * expr

type stmts = stmt list
