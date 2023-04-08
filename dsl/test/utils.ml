open Typecheck
open Coqgen

let test_ty c lib = typecheck_circuit (add_to_deltas [] lib) c

let test (Circuit c' as c : Ast.circuit) lib =
  test_ty c lib |> Coqgen.generate_lemmas c'.name |> print_endline

let testlam_ty lib e = run_synthesis ~gamma:lib e

let testlam name lib e =
  let _, cs = testlam_ty lib e in
  cs |> Coqgen.generate_lemmas name |> print_endline
