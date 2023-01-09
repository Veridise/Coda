#use "circuits/comparators.ml"
#use "circuits/gates.ml"
open Lib__Coqgen

let _ = check_not |> generate_lemmas |> print_endline;;
let _ = check_xor |> generate_lemmas |> print_endline;;
let _ = check_and |> generate_lemmas |> print_endline;;
let _ = check_nand |> generate_lemmas |> print_endline;;
let _ = check_or |> generate_lemmas |> print_endline;;
let _ = check_nor |> generate_lemmas |> print_endline;;