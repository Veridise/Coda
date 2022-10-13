type expr =
  | Sig of int
  | Var of string
  | Opp of expr
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
type arr = expr list

type io =
  | Expr of expr
  | Arr of arr
type io_opt = io option

type stmt =
  | Cons of expr * expr
  | Call of (io_opt -> io_opt -> stmt list) * io_opt * io_opt
  | Map of (expr -> stmt list) * arr
type stmts = stmt list

type circ = io_opt -> io_opt -> stmts
val is_zero: circ
val is_equal: circ
val num2bits: int -> circ
