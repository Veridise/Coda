open Langast.AST
open Langast.Circom

(* transpile AST to Circom *)
let rec transpile_expr (e: Langast.AST.expr) : Langast.Circom.expr =
  match e with 
  | Sig n -> Sig n
  | Var x -> Var x
  | Get (e, i) -> (match i with
                  | ConstInt i -> Get (transpile_expr e, Sig i)
                  | VarInt i -> Get (transpile_expr e, Var i))
  | Opp e -> Opp (transpile_expr e)
  | Add (e1, e2) -> Add (transpile_expr e1, transpile_expr e2)
  | Sub (e1, e2) -> Sub (transpile_expr e1, transpile_expr e2)
  | Mul (e1, e2) -> Mul (transpile_expr e1, transpile_expr e2)
  | Field (e, x) -> Field (transpile_expr e, x)


let rec transpile_iter_var_decl (vars: (string * Langast.AST.expr * Langast.AST.expr) list) : Langast.Circom.stmt list =
  match vars with
  | [] -> []
  | (s, e1, _)::xs -> (VarDef (s, transpile_expr e1))::transpile_iter_var_decl xs

let rec transpile_iter_var_assign (vars: (string * Langast.AST.expr * Langast.AST.expr) list) : Langast.Circom.stmt list =
  match vars with
  | [] -> []
  | (s, _, e2)::xs -> (Assign (Var s, transpile_expr e2))::transpile_iter_var_assign xs

let rec transpile_stmt (s: Langast.AST.stmt) : Langast.Circom.stmt list =
  match s with
  | Constraint (e1, e2) -> [Constraint (transpile_expr e1, transpile_expr e2)]
  | Iter (i, n, l, s) -> List.append (transpile_iter_var_decl l) 
                             [For (VarDef (i, Sig 0), 
                              Lt (Var i, Var n),
                              AddSelf (Var i),
                              List.append (transpile_iter_var_assign l) (transpile_stmt s))]
  | Call (s1, s2) -> [Call (s1, s2)]
  | Map _ -> []
  | Map2 _ -> []

let transpile_varParams (p: Langast.AST.varParams) : Langast.Circom.varParams =
  match p with
  | ConstInt i -> ConstInt i
  | VarInt i -> VarInt i

let transpile_varType (t: Langast.AST.varType) : Langast.Circom.varType =
  match t with
  | Array l -> Array (List.map transpile_varParams l)
  | Expr -> Expr

let transpile_varDecl (v: Langast.AST.varDecl) : Langast.Circom.varDecl =
  match v with
  | Input t -> Input (transpile_varType t)
  | Output t -> Output (transpile_varType t)
  | Signal t -> Signal (transpile_varType t)

(* transpile AST to Circom *)
let transpile (s: Langast.AST.circuit) : Langast.Circom.circuit =
  match s with
  | Template (name, inputs, outputs, stmts) -> 
    Template (name, inputs, List.map (fun x -> (fst x, transpile_varDecl (snd x))) outputs, List.concat (List.map transpile_stmt stmts))
