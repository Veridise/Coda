open Core
open Typecheck
open Circomlib.Comparators

let test c lib = typecheck_circuit (add_to_deltas [] lib) c |> Coqgen.generate_lemmas c |> print_endline
let _ = test is_zero []
let _ = test is_equal [is_zero]
let _ = test less_than Circomlib.[Bitify.num2bits; Gates.cnot]
let _ = test greater_than [less_than]
let _ = test leq [less_than]
let _ = test geq [leq]
