(** * DSL benchmark: Dark Forest *)

(** ** CalculateTotal *)

(* print_endline (generate_lemmas calc_total (typecheck_circuit d_empty calc_total));; *)

(* TODO *)

(** ** QuinSelector *)

(* print_endline (generate_lemmas quin_selector (typecheck_circuit
(add_to_deltas d_empty [c_is_equal; c_less_than; calc_total])
quin_selector));; *)

(* TODO *)

(** IsNegative *)

(* print_endline (generate_lemmas is_neg (typecheck_circuit
(add_to_deltas d_empty [num2bits; c_sign]) is_neg));; *)

(* TODO *)

(** ** Random *)

(* print_endline (generate_lemmas random (typecheck_circuit
(add_to_deltas d_empty [num2bits; mimc_sponge]) random));; *)

(* TODO *)
