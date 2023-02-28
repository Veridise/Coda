(** Cicom AST *)

type varParams =
  | ConstInt of int
  | VarInt of string

type varType = 
  | Array of varParams list (* var x[123][456][789]] ==> Array [ConstInt 123;ConstInt 456;ConstInt 789] *)
  | Expr (* var x; *)

(* Constrainable expressions *)
type expr =
  (* const *)
  | Sig of int
  (* variable *)
  | Var of string
  (* array operation *)
  | Get of expr * expr
  (* unary operation *)
  | Opp of expr
  (* binary operation *)
  | Add of expr * expr
  | AddSelf of expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Lt of expr * expr
  | Shl of expr * expr
  (* template field *)
  | Field of expr * string

(* Circuit inputs and outputs / temp vars *)
type varDecl =
  | Input of varType
  | Output of varType
  | Signal of varType

(* Statements *)
type stmt =
  (* Constraint *)
  | Constraint of expr * expr
  (* Assign *)
  | Assign of expr * expr
  (* var declare *)
  | VarDef of string * expr
  (* for loop*)
  | For of stmt * expr * expr * stmt list 
  | Call of string * string

type stmts = stmt list

(* Circuit: name, (params), (var_name, var_decl), (stmt) *)
type circuit = 
  | Template of string * string list * (string * varDecl) list * stmts

(* print varParams *)
let print_varParams = function
  | ConstInt i -> print_int i
  | VarInt s -> print_string s

(* print varType *)
let print_varType = function
  | Array l -> print_string "Array ["; List.iter (fun x -> print_varParams x; print_string ";") l; print_string "]"
  | Expr -> print_string "Expr"

(* print expr *)
let rec print_expr = function
  | Sig i -> print_int i
  | Var s -> print_string s
  | Get (e1, e2) -> print_string "Get("; print_expr e1; print_string ", "; print_expr e2; print_string ")"
  | Opp e -> print_string "Opp("; print_expr e; print_string ")"
  | Add (e1, e2) -> print_string "Add("; print_expr e1; print_string ", "; print_expr e2; print_string ")"
  | AddSelf e -> print_string "AddSelf("; print_expr e; print_string ")"
  | Sub (e1, e2) -> print_string "Sub("; print_expr e1; print_string ", "; print_expr e2; print_string ")"
  | Mul (e1, e2) -> print_string "Mul("; print_expr e1; print_string ", "; print_expr e2; print_string ")"
  | Shl (e1, e2) -> print_string "Shl("; print_expr e1; print_string ", "; print_expr e2; print_string ")"
  | Lt (e1, e2) -> print_string "Lt("; print_expr e1; print_string ", "; print_expr e2; print_string ")"
  | Field (e, s) -> print_string "Field("; print_expr e; print_string ", "; print_string s; print_string ")"

(* print varDecl *)
let print_varDecl = function
  | Input v -> print_string "Input("; print_varType v; print_string ")"
  | Output v -> print_string "Output("; print_varType v; print_string ")"
  | Signal v -> print_string "Signal("; print_varType v; print_string ")"

(* print stmt *)
let rec print_stmt = function
  | Constraint (e1, e2) -> print_string "Constraint("; print_expr e1; print_string ", "; print_expr e2; print_string ")"
  | Assign (e1, e2) -> print_string "Assign("; print_expr e1; print_string ", "; print_expr e2; print_string ")"
  | VarDef (s, e) -> print_string "VarDef("; print_string s; print_string ", "; print_expr e; print_string ")"
  | For (s1, e1, e2, l) -> print_string "For("; print_stmt s1; print_string ", "; print_expr e1; print_string ", "; print_expr e2; print_string ", "; print_string "["; List.iter (fun x -> print_stmt x; print_string ";") l; print_string "])"
  | Call (s1, s2) -> print_string "Call("; print_string s1; print_string ", "; print_string s2; print_string ")"

(* print stmts *)
let rec print_stmts = function
  | [] -> ()
  | h::t -> print_stmt h; print_string ";"; print_stmts t

(* print circuit *)
let print_circuit = function
  | Template (s, l1, l2, l3) -> print_string "Template("; print_string s; print_string ", "; print_string "["; List.iter (fun x -> print_string x; print_string ";") l1; print_string "]"; print_string ", "; print_string "["; List.iter (fun (x, y) -> print_string "("; print_string x; print_string ", "; print_varDecl y; print_string ")") l2; print_string "]"; print_string ", "; print_string "["; print_stmts l3; print_string "])"


let string_of_list_def c =
  let buf = Buffer.create 1024 in
  let fmt = Format.formatter_of_buffer buf in
  let print s = Format.pp_print_string fmt s in
  let rec iter_list_string l =
    match l with
    | [] -> print ""
    | h::[] -> print h
    | h::xs -> print h; print ", "; iter_list_string xs  in
  iter_list_string c;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

(* pretty-print to string *)
let string_of_circuit c =
  let buf = Buffer.create 1024 in
  let fmt = Format.formatter_of_buffer buf in
  let print s = Format.pp_print_string fmt s in
  let print_int i = Format.pp_print_int fmt i in
  let print_newline () = Format.pp_print_newline fmt () in
  let print_varParams = function
    | ConstInt i -> print_int i
    | VarInt s -> print s
  in
  let print_varType = function
    | Array l -> List.iter (fun x -> print "[";print_varParams x; print "]") l
    | Expr -> print ""
  in
  let rec print_expr = function
    | Sig i -> print_int i
    | Var s -> print s
    | Get (e1, e2) -> print_expr e1; print "["; print_expr e2; print "]"
    | Opp e -> print "("; print "-"; print_expr e; print ")"
    | Add (e1, e2) -> print "("; print_expr e1; print " + "; print_expr e2; print ")"
    | AddSelf e -> print "("; print_expr e; print "++)"
    | Sub (e1, e2) -> print "("; print_expr e1; print " - "; print_expr e2; print ")"
    | Mul (e1, e2) -> print "("; print_expr e1; print " * "; print_expr e2; print ")"
    | Shl (e1, e2) -> print "("; print_expr e1; print " << "; print_expr e2; print ")"
    | Lt (e1, e2) -> print "("; print_expr e1; print " < "; print_expr e2; print ")"
    | Field (e, s) -> print_expr e; print "."; print s
  in
  let rec print_stmts = function
    | [] -> ()
    | h::t -> 
      let rec print_stmt = function
        | Constraint (e1, e2) -> print_expr e1; print " === "; print_expr e2
        | Assign (e1, e2) -> print_expr e1; print " = "; print_expr e2
        | VarDef (s, e) -> print "var "; print s; print " = "; print_expr e
        | For (s1, e1, e2, l) -> print "for ("; print_stmt s1; print "; "; print_expr e1; print "; "; print_expr e2; print ") "; print "{"; print_newline(); print_stmts l; print "}"
        | Call (s1, s2) -> print "component "; print s1; print " = "; print s2; print "()"
      in
      print_stmt h; (match h with | For _ -> print "" | _ -> print ";"); print_newline(); print_stmts t
  in
  let print_str_decl (vdef:string * varDecl) =
    match snd vdef with
    | Input v -> print "signal input "; print (fst vdef); print_varType v
    | Output v -> print "signal output "; print (fst vdef); print_varType v
    | Signal v -> print "signal "; print (fst vdef); print " "; print_varType v
  in
  let print_circuit = function
    | Template (s, l1, l2, l3) -> print "template "; print s; print "("; print (string_of_list_def l1); print ")"; print " {"; print_newline();
                                  List.iter (fun (x, y) -> print_str_decl (x,y); print ";"; print_newline()) l2; 
                                  print_stmts l3; print "}"
  in
  print_circuit c;
  Format.pp_print_flush fmt ();
  Buffer.contents buf