open Langast.AST

let demo target =
  let _ = print_string "=================== DSL ==========================" in
  let _ = print_newline() in
  let _ = Langast.AST.print_circuit target in
  let _ = print_newline() in
  let _ = print_string "=================== DSL ==========================" in
  let _ = print_newline() in
  let _ = print_newline() in
  let _ = print_string "=================== Coq ==========================" in
  let _ = print_newline() in
  let _ = print_string (Langast.AST.string_of_dsl_coq target) in
  let _ = print_newline() in
  let _ = print_string "=================== Coq ==========================" in
  let _ = print_newline() in
  let new_circuit = Transform.transpile target in
  let _ = print_newline() in
  let _ = print_newline() in
  let _ = print_string "=================== Circom ==========================" in
  let _ = print_newline() in
  let _ = print_string (Langast.Circom.string_of_circuit new_circuit) in
  let _ = print_newline() in
  let _ = print_string "=================== Circom ==========================" in
  ()

let _ = demo is_zero; print_newline(); print_newline(); print_newline(); 
        demo is_equal; print_newline(); print_newline(); print_newline();  
        demo num2bits;