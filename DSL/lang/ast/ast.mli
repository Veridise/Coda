type expr =
  | Sig of int
  | Var of string
  | Opp of expr
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
type arry = expr list

type io =
  | Expr of expr
  | Arry of arry
type io_opt = io option

type stmt =
  | Cons of expr * expr
  | Call of (io_opt -> stmt list * io_opt) * io_opt * io_opt
  | Map of (expr -> stmt list) * arry
type stmts = stmt list

type circ = io_opt -> stmts * io_opt
val is_zero: circ
val is_equal: circ
val num2bits: int -> circ
