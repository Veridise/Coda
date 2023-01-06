#use "circuits/comparators.ml"
open Lib__Coqgen

let _ = check_is_zero |> generate_lemmas |> print_endline;;