open Typecheck
open Coqgen

let test_ty c lib = typecheck_circuit (add_to_deltas [] lib) c

let test c lib = test_ty c lib |> Coqgen.generate_lemmas c |> print_endline
