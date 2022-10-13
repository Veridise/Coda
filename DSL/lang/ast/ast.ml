(** DSL abstract syntax tree *)

(* Constrainable expressions *)
type expr =
  | Sig of int
  | Var of string
  | Opp of expr
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr

(* Signal array *)
type arry = expr list

(* Circuit inputs and outputs *)
type io =
  | Expr of expr
  | Arry of arry

type io_opt = io option

(* Statements *)
type stmt =
  (* Constraint *)
  | Cons of expr * expr
  (* Call circuit *)
  | Call of (io_opt -> stmt list * io_opt) * io_opt * io_opt
  (* Map *)
  | Map of (expr -> stmt list) * arry

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
  | Some (Arry [i0; i1]) ->
     let stmts = [
         Call (is_zero, Some (Expr (Sub (i1, i0))), Some (Expr (Var "out")))
       ] in
     (stmts, Some (Expr (Var "out")))
  | _ -> ([], None)

(* Num2Bits *)
let num2bits (n : int) (i : io_opt) : stmts * io_opt =
  match i with
  | Some (Expr e) ->
     let out = List.init n (fun i -> Sig i) in
     let f e' = [ Cons (Mul (e', Sub (e', Sig 1)), Sig 0) ] in
     let stmts = [
         Map (f, out) ;
         Cons (Var "lc1", e)
       ] in
     (stmts, Some (Arry out))
  | _ -> ([], None)
