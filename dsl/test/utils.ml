open Typecheck
open Coqgen

let test_ty c lib  = typecheck_circuit (add_to_deltas [] lib) ~liblam:Liblam.libs_gamma c

let test (Circuit c' as c : Ast.circuit) lib  =
  test_ty c lib |> Coqgen.generate_lemmas c'.name |> print_endline

let testlam_ty liblam e = run_synthesis ~gamma:liblam e

let testlam name liblam e =
  let _, cs = testlam_ty liblam e in
  cs |> Coqgen.generate_lemmas name |> print_endline

let verify_ty ~gamma (l : Liblam.lib) = Typecheck.run_checking ~gamma (Liblam.def l) (Liblam.typ l)

let verify ~gamma (l : Liblam.lib) =
  verify_ty ~gamma l |> Coqgen.generate_lemmas (Liblam.name l) |> print_endline
