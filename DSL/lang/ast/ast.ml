(** DSL abstract syntax tree *)

(* Constrainable expressions *)
type expr =
  | Sig of int
  | Var of string
  | Opp of expr
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr

(* Circuit inputs and outputs *)
type io =
  | Expr of expr
  | List of expr list

type io_opt = io option

(* Statements *)
type stmt =
  (* Constraint *)
  | Cons of expr * expr
  (* Call circuit *)
  | Call of (io_opt -> stmt list * io_opt) * io_opt * io_opt

type stmts = stmt list

(* Circuits *)
type circ = io_opt -> stmts * io_opt

(* IsZero *)
let is_zero (i : io_opt) : stmts * io_opt =
  match i with
  | Some (Expr e) ->
     let stmts = [
         Cons (Var "out", Add (Opp (Mul (e, Var "inv")), Sig 1)) ;
         Cons (Mul (e, Var "out"), Sig 0)
       ] in
     (stmts, Some (Expr (Var "out")))
  | _ -> ([], None)

(* IsEqual *)
let is_equal (i : io_opt) : stmts * io_opt =
  match i with
  | Some (List [i0; i1]) ->
     let stmts = [
         Call (is_zero, Some (Expr (Sub (i1, i0))), Some (Expr (Var "out")))
       ] in
     (stmts, Some (Expr (Var "out")))
  | _ -> ([], None)
