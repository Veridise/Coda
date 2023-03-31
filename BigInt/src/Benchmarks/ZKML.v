(** * DSL benchmark: ZK-ML *)

(** ** Sign *)

(* print_endline (generate_lemmas sign (typecheck_circuit d_empty sign));; *)

(* TODO *)

(** ** IsNegative *)

(* print_endline (generate_lemmas is_negative (typecheck_circuit (add_to_delta d_empty sign) is_negative));; *)

(* TODO *)

(** ** IsPositive (fixed) *)

(* print_endline (generate_lemmas is_positive (typecheck_circuit (add_to_deltas d_empty [c_is_zero; sign]) is_positive));; *)

(* TODO *)

(** ** ReLU *)

(* print_endline (generate_lemmas relu (typecheck_circuit (add_to_delta d_empty is_positive) relu));; *)

Lemma ReLU_obligation0: forall (_in : F) (v : F), True -> True -> ((v = _in) -> True).
Proof. Admitted.

Lemma ReLU_obligation1: forall (_in : F) (isp : F) (v : F), True -> (((isp = 0%F) \/ (isp = 1%F)) /\ (((isp = 1%F) -> (0%nat < (Signed.to_Z _in))) /\ ((isp = 0%F) -> ~(0%nat < (Signed.to_Z _in))))) -> True -> ((v = _in) -> True).
Proof. Admitted.

Lemma ReLU_obligation2: forall (_in : F) (isp : F) (v : F), True -> (((isp = 0%F) \/ (isp = 1%F)) /\ (((isp = 1%F) -> (0%nat < (Signed.to_Z _in))) /\ ((isp = 0%F) -> ~(0%nat < (Signed.to_Z _in))))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (0%nat < (Signed.to_Z _in))) /\ ((v = 0%F) -> ~(0%nat < (Signed.to_Z _in))))) -> ((v = isp) -> True).
Proof. Admitted.

Lemma ReLU_obligation3: forall (_in : F) (isp : F) (v : F), True -> (((isp = 0%F) \/ (isp = 1%F)) /\ (((isp = 1%F) -> (0%nat < (Signed.to_Z _in))) /\ ((isp = 0%F) -> ~(0%nat < (Signed.to_Z _in))))) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (0%nat < (Signed.to_Z _in))) /\ ((v = 0%F) -> ~(0%nat < (Signed.to_Z _in))))) -> True).
Proof. Admitted.

Lemma ReLU_obligation4: forall (_in : F) (isp : F) (v : F), True -> (((isp = 0%F) \/ (isp = 1%F)) /\ (((isp = 1%F) -> (0%nat < (Signed.to_Z _in))) /\ ((isp = 0%F) -> ~(0%nat < (Signed.to_Z _in))))) -> True -> ((v = (_in * isp)%F) -> ((Signed.to_Z v) = (Z.max 0%nat (Signed.to_Z _in)))).
Proof. Admitted.

(** ** Poly *)

(* print_endline (generate_lemmas poly (typecheck_circuit d_empty poly));; *)

Lemma Poly_obligation0: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = _in) -> True).
Proof. Admitted.

Lemma Poly_obligation1: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = _in) -> True).
Proof. Admitted.

Lemma Poly_obligation2: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = (_in * _in)%F) -> True).
Proof. Admitted.

Lemma Poly_obligation3: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = n) -> True).
Proof. Admitted.

Lemma Poly_obligation4: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = _in) -> True).
Proof. Admitted.

Lemma Poly_obligation5: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = (n * _in)%F) -> True).
Proof. Admitted.

Lemma Poly_obligation6: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = ((_in * _in)%F + (n * _in)%F)%F) -> (v = (_in * (_in + n)%F)%F)).
Proof. Admitted.
