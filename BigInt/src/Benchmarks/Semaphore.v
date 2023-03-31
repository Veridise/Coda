(** * DSL benchmark: Semaphore *)

(** ** CalculateSecret *)

(* print_endline (generate_lemmas calc_secret (typecheck_circuit
(add_to_delta d_empty poseidon) calc_secret));; *)

(* TODO *)

(** ** CalculateIdentityCommitment *)

(* print_endline (generate_lemmas calc_id_commit (typecheck_circuit
(add_to_delta d_empty poseidon) calc_id_commit));; *)

(* TODO *)

(** ** CalculateNullifierHash *)

(* print_endline (generate_lemmas calc_null_hash (typecheck_circuit
(add_to_delta d_empty poseidon) calc_null_hash));; *)

(* TODO *)

(** ** MerkleTreeInclusionProof *)

(* print_endline (generate_lemmas mrkl_tree_incl_pf (typecheck_circuit
(add_to_deltas d_empty [poseidon; multi_mux_1]) mrkl_tree_incl_pf));; *)

(* TODO *)

(** ** Semaphore *)

(* print_endline (generate_lemmas semaphore (typecheck_circuit
(add_to_deltas d_empty [poseidon; calc_secret; calc_id_commit;
calc_null_hash; mrkl_tree_incl_pf]) semaphore));; *)

(* TODO *)
