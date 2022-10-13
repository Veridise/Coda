(** DSL AST *)

(* Constrainable expressions *)
type expr =
  | Sig of int
  | Var of string
  | Opp of expr
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr

(* Signal array *)
type arr = expr list

(* Circuit inputs and outputs *)
type io =
  | Expr of expr
  | Arr of arr

type io_opt = io option

(* Statements *)
type stmt =
  (* Constraint *)
  | Cons of expr * expr
  (* Call circuit *)
  | Call of (io_opt -> io_opt -> stmt list) * io_opt * io_opt
  (* Map *)
  | Map of (expr -> stmt list) * arr

type stmts = stmt list

(* Circuits *)
type circ = io_opt -> io_opt -> stmts

(* IsZero *)
let is_zero i o =
  match i, o with
  | Some (Expr i), Some (Expr o) -> [
      Cons (o, Add (Opp (Mul (i, Var "inv")), Sig 1)) ;
      Cons (Mul (i, o), Sig 0)
    ]
  | _ -> []

(* IsEqual *)
let is_equal i o =
  match i, o with
  | Some (Arr [i0; i1]), Some (Expr o) -> [
      Call (is_zero, Some (Expr (Sub (i1, i0))), Some (Expr o))
    ]
  | _ -> []

(* Num2Bits *)
let num2bits n i o =
  match i, o with
  | Some (Expr i), Some (Arr o) when List.length o = n ->
     let f e = [ Cons (Mul (e, Sub (e, Sig 1)), Sig 0) ] in
     [ Map (f, o) ; Cons (Var "lc1", i) ]
  | _ -> []
