(** * DSL benchmark: ZK-SQL *)

(** ** CalculateTotal *)

(* print_endline (generate_lemmas calc_total (typecheck_circuit d_empty calc_total));; *)

(* TODO *)

(** ** SumEquals *)

(* print_endline (generate_lemmas sum_equals (typecheck_circuit (add_to_deltas d_empty [c_is_equal; calc_total]) sum_equals));; *)

(* TODO *)

(** ** IsNotZero *)

(* print_endline (generate_lemmas is_not_zero (typecheck_circuit (add_to_deltas d_empty [cnot; c_is_zero]) is_not_zero));; *)

Lemma IsNotZero_obligation0: forall (_in : F) (v : F), True -> True -> ((v = _in) -> True).
Proof. Admitted.

Lemma IsNotZero_obligation1: forall (_in : F) (isz : F) (v : F), True -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (_in = 0%F)) /\ ((v = 0%F) -> ~(_in = 0%F)))) -> ((v = isz) -> ((v = 0%F) \/ (v = 1%F))).
Proof. Admitted.

Lemma IsNotZero_obligation2: forall (_in : F) (isz : F) (v : F), True -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (_in = 0%F)) /\ ((v = 0%F) -> ~(_in = 0%F)))) -> True).
Proof. Admitted.

Lemma IsNotZero_obligation3: forall (_in : F) (isz : F) (v : F), True -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_not isz)) /\ ((v = 0%F) -> ~(f_not isz)))) -> (True -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ~(_in = 0%F)) /\ ((v = 0%F) -> ~~(_in = 0%F))))).
Proof. Admitted.

Lemma IsNotZero_obligation4: forall (_in : F) (isz : F) (v : F), True -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_not isz)) /\ ((v = 0%F) -> ~(f_not isz)))) -> True).
Proof. Admitted.

(** ** IsFiltered *)

(* print_endline (generate_lemmas is_filtered (typecheck_circuit (add_to_deltas d_empty [c_is_equal; calc_total]) is_filtered));; *)

(* TODO *)
