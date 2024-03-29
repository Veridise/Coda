open Coqgen ;;

#use "circuits/trivial.ml"

let _ = check_c_assert_equal |> generate_lemmas |> print_endline

(* let _ = check_c_dep_caller |> generate_lemmas |> print_endline;; *)
let _ = check_c_assert_binary |> generate_lemmas |> print_endline

(* #use "circuits/gates.ml"

   let _ = check_not |> generate_lemmas |> print_endline;;
   let _ = check_xor |> generate_lemmas |> print_endline;;
   let _ = check_and |> generate_lemmas |> print_endline;;
   let _ = check_nand |> generate_lemmas |> print_endline;;
   let _ = check_or |> generate_lemmas |> print_endline;;
   let _ = check_nor |> generate_lemmas |> print_endline;;

   #use "circuits/bitify.ml"

   #use "circuits//comparators.ml"
   (* let check_lt = typecheck_circuit (add_to_delta d_empty num2bits) c_lt *)
   (* let _ = check_lt |> generate_lemmas |> print_endline *)
   (* let _ = check_is_zero |> generate_lemmas |> print_endline;; *)
   (* let _ = check_is_equal |> generate_lemmas |> print_endline;; *)

   #use "circuits/biglessthan.ml"
   let check_big_lt = big_lt
     |> typecheck_circuit (add_to_deltas d_empty [cand;cor;is_equal;less_than])
     |> filter_trivial

   let _ = check_big_lt  |> generate_lemmas |> print_endline;; *)
