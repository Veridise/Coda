(** * DSL benchmark: Hydra-S1 ZKPS *)

(** ** PositionSwitcher *)

(* print_endline (generate_lemmas position_switcher (typecheck_circuit
d_empty position_switcher));; *)

(* TODO *)

(** ** VerifyMerklePath *)

(* print_endline (generate_lemmas vrfy_mrkl_path (typecheck_circuit
(add_to_deltas d_empty [poseidon; position_switcher])
vrfy_mrkl_path));; *)

(* TODO *)

(** ** VerifyHydraCommitment *)

(* print_endline (generate_lemmas vrfy_hydra_commit (typecheck_circuit
(add_to_deltas d_empty [poseidon; vrfy_eddsa_poseidon])
vrfy_hydra_commit));; *)

(* TODO *)

(** ** hydraS1 *)

(* print_endline (generate_lemmas hydra_s1 (typecheck_circuit
(add_to_deltas d_empty [num2bits; c_less_eq_than; poseidon;
vrfy_hydra_commit; vrfy_mrkl_path]) hydra_s1));; *)

(* TODO *)
