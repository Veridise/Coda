(** DSL AST *)

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
  | Get of expr * varParams
  (* unary operation *)
  | Opp of expr
  (* binary operation *)
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  (* template field *)
  | Field of expr * string

(* Circuit inputs and outputs / temp vars *)
type varDecl =
  | Input of varType
  | Output of varType
  | Signal of varType

(* Statements *)
type stmt =
  (* call: name, template *)
  | Call of string * string
  (* e1 === e2 *)
  | Constraint of expr * expr
  (* iter index range_max (var_name, expr, expr) stmt *)
  | Iter of string * string * (string * expr * expr) list * stmt
  (* map (fun x -> stmts) xs *)
  | Map of (string * varType) * stmt list * expr
  (* map2 (fun x y -> stmts) xs ys *)
  | Map2 of (string * string * varType) * stmt list * expr * expr

type stmts = stmt list

(* Circuit: name, (params), (var_name, var_decl), (stmt) *)
type circuit = 
  | Template of string * string list * (string * varDecl) list * stmts

(* Program *)
type program = circuit list

(* Environment: for typechecking *)
type env = string -> ((string * varDecl) list) option

(* generate environment from program *)
let genv (p: program) : env =
  let rec genv' (p: program) (e: env) : env =
    match p with
    | [] -> e
    | (Template (name, _, vars, _))::p' -> 
        genv' p' (fun x -> if x = name then Some vars else e x)
  in genv' p (fun _ -> None)

(* print varParams *)
let print_varParams (v: varParams) : unit =
  match v with
  | ConstInt i -> print_int i
  | VarInt s -> print_string s

(* print varType *)
let print_varType (v: varType) : unit =
  match v with
  | Array l -> 
      print_string "Array [";
      List.iter (fun x -> print_varParams x; print_string ";") l;
      print_string "]"
  | Expr -> print_string "Expr"

(* print expr *)
let rec print_expr (e: expr) : unit =
  match e with
  | Sig i -> print_int i
  | Var s -> print_string s
  | Get (e, v) -> 
      print_string "Get (";
      print_expr e;
      print_string ", ";
      print_varParams v;
      print_string ")"
  | Opp e -> 
      print_string "Opp (";
      print_expr e;
      print_string ")"
  | Add (e1, e2) -> 
      print_string "Add (";
      print_expr e1;
      print_string ", ";
      print_expr e2;
      print_string ")"
  | Sub (e1, e2) -> 
      print_string "Sub (";
      print_expr e1;
      print_string ", ";
      print_expr e2;
      print_string ")"
  | Mul (e1, e2) -> 
      print_string "Mul (";
      print_expr e1;
      print_string ", ";
      print_expr e2;
      print_string ")"
  | Field (e, s) -> 
      print_string "Field (";
      print_expr e;
      print_string ", ";
      print_string s;
      print_string ")"

(* print varDecl *)
let print_varDecl (v: varDecl) : unit =
  match v with
  | Input t -> 
      print_string "Input (";
      print_varType t;
      print_string ")"
  | Output t -> 
      print_string "Output (";
      print_varType t;
      print_string ")"
  | Signal t -> 
      print_string "Signal (";
      print_varType t;
      print_string ")"

(* print stmt *)
let rec print_stmt (s: stmt) : unit =
  match s with
  | Constraint (e1, e2) -> 
      print_string "Constraint (";
      print_expr e1;
      print_string ", ";
      print_expr e2;
      print_string ")"
  | Iter (s1, s2, l, s3) -> 
      print_string "Iter (";
      print_string s1;
      print_string ", ";
      print_string s2;
      print_string ", [";
      List.iter (fun (s, e1, e2) -> 
        print_string "(";
        print_string s;
        print_string ", ";
        print_expr e1;
        print_string ", ";
        print_expr e2;
        print_string ");") l;
      print_string "], ";
      print_stmt s3;
      print_string ")"
  | Call (s1, s2) ->
      print_string "Call (";
      print_string s1;
      print_string ", ";
      print_string s2;
      print_string ")"
  | Map _ -> ()
  | Map2 _ -> ()

(* print stmts *)
let rec print_stmts (s: stmts) : unit =
  match s with
  | [] -> ()
  | s::s' -> 
      print_stmt s;
      print_string ";";
      print_stmts s'

(* print circuit *)
let print_circuit (c: circuit) : unit =
  match c with
  | Template (s, l, l', s') -> 
      print_string "Template (";
      print_string s;
      print_string ", [";
      List.iter (fun x -> print_string x; print_string ";") l;
      print_string "], [";
      List.iter (fun (s, v) -> 
        print_string "(";
        print_string s;
        print_string ", ";
        print_varDecl v;
        print_string ");") l';
      print_string "], ";
      print_stmts s';
      print_string ")"

(* print program *)
let rec print_program (p: program) : unit =
  match p with
  | [] -> ()
  | c::c' -> 
      print_circuit c;
      print_string ";";
      print_program c'

(* print to Coq *)
let string_of_dsl_coq c =
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
    | Array l -> print "F"; List.iter (fun x -> print "^";print_varParams x) l (* todo: nested *)
    | Expr -> print "F"
  in
  let rec print_expr = function
    | Sig i -> print_int i
    | Var s -> print s
    | Get (e1, e2) -> print_expr e1; print "["; print_varParams e2; print "]"
    | Opp e -> print "("; print "-"; print_expr e; print ")"
    | Add (e1, e2) -> print "("; print_expr e1; print " + "; print_expr e2; print ")"
    | Sub (e1, e2) -> print "("; print_expr e1; print " - "; print_expr e2; print ")"
    | Mul (e1, e2) -> print "("; print_expr e1; print " * "; print_expr e2; print ")"
    | Field (e, s) -> print_expr e; print "."; print s
  in
  let rec print_loop_decl = function
    | [] -> ()
    | (s, _, _)::[] -> print s;
    | (s, _, _)::l -> print s; print ", "; print_loop_decl l
  in
  let rec print_loop_decl_init = function
      | [] -> ()
      | (_, s, _)::[] -> print_expr s;
      | (_, s, _)::l -> print_expr s; print ", "; print_loop_decl_init l
  in
  let rec print_loop_decl_iter = function
      | [] -> ()
      | (_, _, s)::[] -> print_expr s;
      | (_, _, s)::l -> print_expr s; print ", "; print_newline(); print_loop_decl_iter l
  in
  let rec print_stmts = 
    function
    | [] -> ()
    | h::[] -> 
      let rec print_stmt = function
        | Constraint (e1, e2) -> print_expr e1; print " = "; print_expr e2;
        | Iter (_, s2, l, s3) -> 
          print "let '("; print_loop_decl l; print ", _C) :="; print "(D.iter (fun ("; print s2; print ": nat) '("; print_loop_decl l; print ", _C) => "; print_newline(); 
          print "("; print_loop_decl_iter l; print ", "; print_newline(); print_stmt s3; print "/\\ _C)";print_newline();
          print ") "; print "(";print_loop_decl_init l; print ", True)) in _C /\\";
        | Call (s1, s2) -> print "exists ("; print s1; print ": "; print s2; print ".t),"
        | Map _ -> ()
        | Map2 _ -> ()
      in
      print_stmt h; print_newline();
    | h::t -> 
      let rec print_stmt = function
        | Constraint (e1, e2) -> print_expr e1; print " = "; print_expr e2;
        | Iter (_, s2, l, s3) -> 
          print "let '("; print_loop_decl l; print ", _C) :="; print "(D.iter (fun ("; print s2; print ": nat) '("; print_loop_decl l; print ", _C) => "; print_newline(); 
          print "("; print_loop_decl_iter l; print ", "; print_newline(); print_stmt s3; print "/\\ _C)";print_newline();
          print ") "; print "(";print_loop_decl_init l; print ", True)) in _C /\\";
        | Call (s1, s2) -> print "exists ("; print s1; print ": "; print s2; print ".t),"
        | Map _ -> ()
        | Map2 _ -> ()
      in
      print_stmt h; (match h with | Call _ -> print "" | Iter _ -> print "" | _ -> print " /\\ "); print_newline(); print_stmts t
  in
  let print_str_decl (vdef:string * varDecl) =
    match snd vdef with
    | Input v -> print (fst vdef); print ": "; print_varType v
    | Output v -> print (fst vdef); print ": "; print_varType v
    | Signal v -> print (fst vdef); print ": "; print_varType v
  in
  let print_str_decl_record (vdef:string * varDecl) =
    match snd vdef with
    | Input v -> print (fst vdef); print ": "; print_varType v
    | Output v -> print (fst vdef); print ": "; print_varType v
    | Signal _ -> print ""
  in
  let print_str_decl_record1 (vdef:string * varDecl) =
    match snd vdef with
    | Input _ -> print ""
    | Output _ -> print ""
    | Signal _ -> print "exists "; print (fst vdef); print ", "
  in
  let print_circuit = function
    | Template (s, l1, l2, l3) -> print "Module "; print s; print "."; print_newline(); print_newline();
                                  List.iter (fun (x) -> print "Context {"; print x; print " : nat}."; print_newline()) l1; 
                                  print "Definition cons ";
                                  List.iter (fun (x, y) -> print " ("; print_str_decl (x,y); print ") ") l2;  print ":="; print_newline();
                                  print_stmts l3; print "."; print_newline();print_newline();
                                  print "Record t : Type := { "; List.iter (fun (x, y) -> print_str_decl_record (x,y); print "; ") l2; 
                                  print "_cons: ";List.iter (fun (x, y) -> print_str_decl_record1 (x,y)) l2;
                                  print "cons "; List.iter (fun (x, _) -> print x; print " ") l2; print "}.";print_newline();print_newline();
                                  print "End "; print s; print ".";
  in
  print_circuit c;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

(* Examples *)
let is_zero = 
  Template ("IsZero", [],
            [("_in", Input Expr);
             ("out", Output Expr);
             ("_inv", Signal Expr)], 
            [Constraint (Var "out", Add (Opp (Mul (Var "_in", Var "_inv")), Sig 1));
             Constraint (Mul (Var "_in", Var "out"), Sig 0)])

let is_equal =
  Template ("IsEqual", [],
            [("_in", Input (Array [ConstInt 2]));
             ("out", Output Expr);],
            [Call ("isz", "IsZero");
             Constraint (Sub (Get (Var "_in", ConstInt 1), Get (Var "_in", ConstInt 0)), Field (Var "isz", "_in"));
             Constraint (Var "out", Field (Var "isz", "out"))])

let num2bits =
  Template ("Num2Bits", ["n"],
            [("_in", Input Expr);
             ("out", Output (Array [VarInt "n"]))],
            [Iter ("i", "n",
                   [("lc1", Sig 0, Add (Var "lc1", Mul (Get (Var "out", VarInt "i"), Var "e2")));
                    ("e2", Sig 1, Add (Var "e2", Var "e2"))],
                   Constraint (Mul (Get (Var "out", VarInt "i"), Sub (Get (Var "out", VarInt "i"), Sig 1)), Sig 0));
             Constraint (Var "lc1", Var "_in")])

let num2bits_map =
  Template ("Num2Bits", ["n"],
            [("_in", Input Expr);
             ("out", Output (Array [VarInt "n"]))],
            [Map (("x", Expr),
                  [Constraint (Mul (Var "x", Sub (Var "x", Sig 1)), Sig 0)],
                  Var "out");
             Constraint (Var "lc1", Var "_in")])
