(** * DSL benchmark: ZK-SBT *)

(** ** IN *)

(* print_endline (generate_lemmas c_in (typecheck_circuit
(add_to_deltas d_empty [c_is_equal; c_greater_than]) c_in));; *)

(* TODO *)

(** ** Query *)

(* print_endline (generate_lemmas query (typecheck_circuit
(add_to_deltas d_empty [num2bits; c_is_equal; c_less_than;
c_greater_than; mux3; c_in]) query));; *)

(* TODO *)

(** ** getValueByIndex *)

(* print_endline (generate_lemmas get_val_by_idx (typecheck_circuit
(add_to_deltas d_empty [num2bits; mux3]) get_val_by_idx));; *)

(* TODO *)

(** ** getIdenState *)

(* print_endline (generate_lemmas get_iden_state (typecheck_circuit
(add_to_delta d_empty poseidon) get_iden_state));; *)

(* TODO *)

(** ** cutId *)

(* print_endline (generate_lemmas cut_id (typecheck_circuit
(add_to_deltas d_empty [num2bits; bits2num]) cut_id));; *)

(* TODO *)

(** ** cutState *)

(* print_endline (generate_lemmas cut_st (typecheck_circuit
(add_to_deltas d_empty [num2bits; bits2num]) cut_st));; *)

(* TODO *)
