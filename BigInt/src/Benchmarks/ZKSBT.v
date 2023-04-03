(** * DSL benchmark: ZK-SBT *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems Crypto.Algebra.Field.
Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.

From Circom Require Import Circom Util Default Tuple ListUtil LibTactics Simplify Repr.
From Circom.CircomLib Require Import Bitify.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

(** ** IN *)

(* print_endline (generate_lemmas c_in (typecheck_circuit (add_to_deltas d_empty [is_equal; greater_than]) c_in));; *)

Lemma IN_obligation0_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (v : Z), True -> Forall (fun x0 => True) value -> ((length value) = valueArraySize) -> True -> ((v = 0%nat) -> True).
Proof. intuit. Qed.

Lemma IN_obligation1_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (v : Z), True -> Forall (fun x1 => True) value -> ((length value) = valueArraySize) -> True -> (((0%nat <= v) /\ (v = valueArraySize)) -> True).
Proof. intuit. Qed.

Lemma IN_obligation2_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (v : Z), True -> Forall (fun x2 => True) value -> ((length value) = valueArraySize) -> True -> (((0%nat <= v) /\ (v < valueArraySize)) -> True).
Proof. intuit. Qed.

Lemma IN_obligation3_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (i : nat) (v : F), True -> Forall (fun x3 => True) value -> ((length value) = valueArraySize) -> (i < valueArraySize) -> True -> (((v = 0%F) -> (forall (j:nat), 0%nat <= j < i -> ~(((value!j) = _in)))) -> True).
Proof. intuit. Qed.

Lemma IN_obligation4_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (i : nat) (x : F) (v : F), True -> Forall (fun x4 => True) value -> ((length value) = valueArraySize) -> (i < valueArraySize) -> ((x = 0%F) -> (forall (j:nat), 0%nat <= j < i -> ~(((value!j) = _in)))) -> True -> ((v = _in) -> True).
Proof. intuit. Qed.

Lemma IN_obligation5_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (i : nat) (x : F) (v : F), True -> Forall (fun x5 => True) value -> ((length value) = valueArraySize) -> (i < valueArraySize) -> ((x = 0%F) -> (forall (j:nat), 0%nat <= j < i -> ~(((value!j) = _in)))) -> True -> ((v = (value!i)) -> True).
Proof. intuit. Qed.

Lemma IN_obligation6_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (i : nat) (x : F) (ise : F) (v : F), True -> Forall (fun x6 => True) value -> ((length value) = valueArraySize) -> (i < valueArraySize) -> ((x = 0%F) -> (forall (j:nat), 0%nat <= j < i -> ~(((value!j) = _in)))) -> (((ise = 0%F) \/ (ise = 1%F)) /\ (((ise = 1%F) -> (_in = (value!i))) /\ ((ise = 0%F) -> ~(_in = (value!i))))) -> True -> ((((v = 0%F) -> (forall (j:nat), 0%nat <= j < i -> ~(((value!j) = _in)))) /\ (v = x)) -> True).
Proof. intuit. Qed.

Lemma IN_obligation7_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (i : nat) (x : F) (ise : F) (v : F), True -> Forall (fun x7 => True) value -> ((length value) = valueArraySize) -> (i < valueArraySize) -> ((x = 0%F) -> (forall (j:nat), 0%nat <= j < i -> ~(((value!j) = _in)))) -> (((ise = 0%F) \/ (ise = 1%F)) /\ (((ise = 1%F) -> (_in = (value!i))) /\ ((ise = 0%F) -> ~(_in = (value!i))))) -> True -> (((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (_in = (value!i))) /\ ((v = 0%F) -> ~(_in = (value!i))))) /\ (v = ise)) -> True).
Proof. intuit. Qed.

Lemma IN_obligation8: forall (valueArraySize : nat) (_in : F) (value : (list F)) (i : nat) (x : F) (ise : F) (v : F), True -> Forall (fun x8 => True) value -> ((length value) = valueArraySize) -> (i < valueArraySize) -> ((x = 0%F) -> (forall (j:nat), 0%nat <= j < i -> ~(((value!j) = _in)))) -> (((ise = 0%F) \/ (ise = 1%F)) /\ (((ise = 1%F) -> (_in = (value!i))) /\ ((ise = 0%F) -> ~(_in = (value!i))))) -> True -> ((v = (x + ise)%F) -> ((v = 0%F) -> (forall (j:nat), 0%nat <= j < (i + 1%nat)%nat -> ~(((value!j) = _in))))).
Proof. Admitted.

Lemma IN_obligation9: forall (valueArraySize : nat) (_in : F) (value : (list F)) (v : F), True -> Forall (fun x9 => True) value -> ((length value) = valueArraySize) -> True -> ((v = 0%F) -> ((v = 0%F) -> (forall (j:nat), 0%nat <= j < 0%nat -> ~(((value!j) = _in))))).
Proof. Admitted.

Lemma IN_obligation10: forall (valueArraySize : nat) (_in : F) (value : (list F)) (count : F) (v : Z), True -> Forall (fun x10 => True) value -> ((length value) = valueArraySize) -> ((count = 0%F) -> (forall (j:nat), 0%nat <= j < valueArraySize -> ~(((value!j) = _in)))) -> True -> ((v = 252%nat) -> ((0%nat <= v) /\ (v < (C.k - 1%nat)%Z))).
Proof. Admitted.

Lemma IN_obligation11: forall (valueArraySize : nat) (_in : F) (value : (list F)) (count : F) (v : F), True -> Forall (fun x11 => True) value -> ((length value) = valueArraySize) -> ((count = 0%F) -> (forall (j:nat), 0%nat <= j < valueArraySize -> ~(((value!j) = _in)))) -> True -> ((((v = 0%F) -> (forall (j:nat), 0%nat <= j < valueArraySize -> ~(((value!j) = _in)))) /\ (v = count)) -> (F.to_Z v < (2%nat ^ 252%nat)%Z)).
Proof. Admitted.

Lemma IN_obligation12: forall (valueArraySize : nat) (_in : F) (value : (list F)) (count : F) (v : F), True -> Forall (fun x12 => True) value -> ((length value) = valueArraySize) -> ((count = 0%F) -> (forall (j:nat), 0%nat <= j < valueArraySize -> ~(((value!j) = _in)))) -> True -> ((v = 0%F) -> (F.to_Z v < (2%nat ^ 252%nat)%Z)).
Proof. Admitted.

Lemma IN_obligation13: forall (valueArraySize : nat) (_in : F) (value : (list F)) (count : F) (v : F), True -> Forall (fun x13 => True) value -> ((length value) = valueArraySize) -> ((count = 0%F) -> (forall (j:nat), 0%nat <= j < valueArraySize -> ~(((value!j) = _in)))) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (F.to_Z 0%F < F.to_Z count)) /\ ((v = 0%F) -> ~(F.to_Z 0%F < F.to_Z count)))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ~((forall (i:nat), 0%nat <= i < (length value) -> ~(((value!i) = _in))))) /\ ((v = 0%F) -> ~(~((forall (i:nat), 0%nat <= i < (length value) -> ~(((value!i) = _in))))))))).
Proof. Admitted.

(** ** Query *)

(* print_endline (generate_lemmas query (typecheck_circuit (add_to_deltas d_empty [num2bits; is_equal; less_than; greater_than; mux3; c_in]) query));; *)

Lemma Query_obligation0_trivial: forall (valueArraySize : Z) (_in : F) (value : (list F)) (operator : F) (x : F) (v : F), (0%nat < valueArraySize) -> True -> Forall (fun x24 => True) value -> ((length value) = valueArraySize) -> True -> (x = (value!0%nat)) -> True -> ((v = _in) -> True).
Proof. intuit. Qed.

Lemma Query_obligation1_trivial: forall (valueArraySize : Z) (_in : F) (value : (list F)) (operator : F) (x : F) (v : F), (0%nat < valueArraySize) -> True -> Forall (fun x25 => True) value -> ((length value) = valueArraySize) -> True -> (x = (value!0%nat)) -> True -> (((v = (value!0%nat)) /\ (v = x)) -> True).
Proof. intuit. Qed.

Lemma Query_obligation2: forall (valueArraySize : Z) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (v : Z), (0%nat < valueArraySize) -> True -> Forall (fun x26 => True) value -> ((length value) = valueArraySize) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> True -> ((v = 252%nat) -> ((0%nat <= v) /\ (v < (C.k - 1%nat)%Z))).
Proof. Admitted.

Lemma Query_obligation3: forall (valueArraySize : Z) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (v : F), (0%nat < valueArraySize) -> True -> Forall (fun x27 => True) value -> ((length value) = valueArraySize) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> True -> ((v = _in) -> ((^ v) < (2%nat ^ 252%nat)%Z)).
Proof. Admitted.

Lemma Query_obligation4: forall (valueArraySize : Z) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (v : F), (0%nat < valueArraySize) -> True -> Forall (fun x28 => True) value -> ((length value) = valueArraySize) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> True -> (((v = (value!0%nat)) /\ (v = x)) -> ((^ v) < (2%nat ^ 252%nat)%Z)).
Proof. Admitted.

Lemma Query_obligation5: forall (valueArraySize : Z) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (v : Z), (0%nat < valueArraySize) -> True -> Forall (fun x29 => True) value -> ((length value) = valueArraySize) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> True -> ((v = 252%nat) -> ((0%nat <= v) /\ (v < (C.k - 1%nat)%Z))).
Proof. Admitted.

Lemma Query_obligation6: forall (valueArraySize : Z) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (v : F), (0%nat < valueArraySize) -> True -> Forall (fun x30 => True) value -> ((length value) = valueArraySize) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> True -> ((v = _in) -> ((^ v) < (2%nat ^ 252%nat)%Z)).
Proof. Admitted.

Lemma Query_obligation7: forall (valueArraySize : Z) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (v : F), (0%nat < valueArraySize) -> True -> Forall (fun x31 => True) value -> ((length value) = valueArraySize) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> True -> (((v = (value!0%nat)) /\ (v = x)) -> ((^ v) < (2%nat ^ 252%nat)%Z)).
Proof. Admitted.

Lemma Query_obligation8: forall (valueArraySize : Z) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (gt : F) (v : Z), (0%nat < valueArraySize) -> True -> Forall (fun x32 => True) value -> ((length value) = valueArraySize) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ x) < (^ _in))) /\ ((gt = 0%F) -> ~((^ x) < (^ _in))))) -> True -> (((0%nat < v) /\ (v = valueArraySize)) -> (0%nat <= v)).
Proof. Admitted.

Lemma Query_obligation9_trivial: forall (valueArraySize : Z) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (gt : F) (v : F), (0%nat < valueArraySize) -> True -> Forall (fun x33 => True) value -> ((length value) = valueArraySize) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ x) < (^ _in))) /\ ((gt = 0%F) -> ~((^ x) < (^ _in))))) -> True -> ((v = _in) -> True).
Proof. intuit. Qed.

Lemma Query_obligation10: forall (valueArraySize : Z) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (gt : F) (v : (list F)), (0%nat < valueArraySize) -> True -> Forall (fun x34 => True) value -> ((length value) = valueArraySize) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ x) < (^ _in))) /\ ((gt = 0%F) -> ~((^ x) < (^ _in))))) -> Forall (fun x35 => True) v -> True -> ((((length v) = valueArraySize) /\ (v = value)) -> ((length v) = valueArraySize)).
Proof. Admitted.

Lemma Query_obligation11: forall (valueArraySize : Z) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (gt : F) (_in : F) (v : Z), (0%nat < valueArraySize) -> True -> Forall (fun x36 => True) value -> ((length value) = valueArraySize) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ x) < (^ _in))) /\ ((gt = 0%F) -> ~((^ x) < (^ _in))))) -> (((_in = 0%F) \/ (_in = 1%F)) /\ (((_in = 1%F) -> (exists (i:nat), 0%nat <= i < (length value) -> ((value!i) = _in))) /\ ((_in = 0%F) -> ~((exists (i:nat), 0%nat <= i < (length value) -> ((value!i) = _in)))))) -> True -> ((v = 3%nat) -> (0%nat <= v)).
Proof. Admitted.

Lemma Query_obligation12_trivial: forall (valueArraySize : Z) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (gt : F) (_in : F) (v : F), (0%nat < valueArraySize) -> True -> Forall (fun x37 => True) value -> ((length value) = valueArraySize) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ x) < (^ _in))) /\ ((gt = 0%F) -> ~((^ x) < (^ _in))))) -> (((_in = 0%F) \/ (_in = 1%F)) /\ (((_in = 1%F) -> (exists (i:nat), 0%nat <= i < (length value) -> ((value!i) = _in))) /\ ((_in = 0%F) -> ~((exists (i:nat), 0%nat <= i < (length value) -> ((value!i) = _in)))))) -> True -> ((v = operator) -> True).
Proof. intuit. Qed.

Lemma Query_obligation13: forall (valueArraySize : Z) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (gt : F) (_in : F) (n2b : (list F)) (v : (list F)), (0%nat < valueArraySize) -> True -> Forall (fun x38 => True) value -> ((length value) = valueArraySize) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ x) < (^ _in))) /\ ((gt = 0%F) -> ~((^ x) < (^ _in))))) -> (((_in = 0%F) \/ (_in = 1%F)) /\ (((_in = 1%F) -> (exists (i:nat), 0%nat <= i < (length value) -> ((value!i) = _in))) /\ ((_in = 0%F) -> ~((exists (i:nat), 0%nat <= i < (length value) -> ((value!i) = _in)))))) -> Forall (fun x39 => ((x39 = 0%F) \/ (x39 = 1%F))) n2b -> (((as_le_f n2b) = operator) /\ ((length n2b) = 3%nat)) -> Forall (fun x40 => True) v -> True -> ((((((((((True /\ ((v!0%nat) = 1%F)) /\ ((v!1%nat) = eq)) /\ ((v!2%nat) = lt)) /\ ((v!3%nat) = gt)) /\ ((v!4%nat) = _in)) /\ ((v!5%nat) = (1%F - _in)%F)) /\ ((v!6%nat) = 0%F)) /\ ((v!7%nat) = 0%F)) /\ ((length v) = 8%nat)) -> ((length v) = 8%nat)).
Proof. Admitted.

Lemma Query_obligation14: forall (valueArraySize : Z) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (gt : F) (_in : F) (n2b : (list F)) (v : (list F)), (0%nat < valueArraySize) -> True -> Forall (fun x41 => True) value -> ((length value) = valueArraySize) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ x) < (^ _in))) /\ ((gt = 0%F) -> ~((^ x) < (^ _in))))) -> (((_in = 0%F) \/ (_in = 1%F)) /\ (((_in = 1%F) -> (exists (i:nat), 0%nat <= i < (length value) -> ((value!i) = _in))) /\ ((_in = 0%F) -> ~((exists (i:nat), 0%nat <= i < (length value) -> ((value!i) = _in)))))) -> Forall (fun x42 => ((x42 = 0%F) \/ (x42 = 1%F))) n2b -> (((as_le_f n2b) = operator) /\ ((length n2b) = 3%nat)) -> Forall (fun x43 => ((x43 = 0%F) \/ (x43 = 1%F))) v -> True -> (((((as_le_f v) = operator) /\ ((length v) = 3%nat)) /\ (v = n2b)) -> ((length v) = 3%nat)).
Proof. Admitted.

Lemma Query_obligation15_trivial: forall (valueArraySize : Z) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (gt : F) (_in : F) (n2b : (list F)) (v : F), (0%nat < valueArraySize) -> True -> Forall (fun x44 => True) value -> ((length value) = valueArraySize) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ x) < (^ _in))) /\ ((gt = 0%F) -> ~((^ x) < (^ _in))))) -> (((_in = 0%F) \/ (_in = 1%F)) /\ (((_in = 1%F) -> (exists (i:nat), 0%nat <= i < (length value) -> ((value!i) = _in))) /\ ((_in = 0%F) -> ~((exists (i:nat), 0%nat <= i < (length value) -> ((value!i) = _in)))))) -> Forall (fun x45 => ((x45 = 0%F) \/ (x45 = 1%F))) n2b -> (((as_le_f n2b) = operator) /\ ((length n2b) = 3%nat)) -> True -> (((v = 0%F) \/ (v = 1%F)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. intuit. Qed.

Lemma Query_obligation16: forall (valueArraySize : Z) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (gt : F) (_in : F) (n2b : (list F)) (v : F), (0%nat < valueArraySize) -> True -> Forall (fun x46 => True) value -> ((length value) = valueArraySize) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ x) < (^ _in))) /\ ((gt = 0%F) -> ~((^ x) < (^ _in))))) -> (((_in = 0%F) \/ (_in = 1%F)) /\ (((_in = 1%F) -> (exists (i:nat), 0%nat <= i < (length value) -> ((value!i) = _in))) /\ ((_in = 0%F) -> ~((exists (i:nat), 0%nat <= i < (length value) -> ((value!i) = _in)))))) -> Forall (fun x47 => ((x47 = 0%F) \/ (x47 = 1%F))) n2b -> (((as_le_f n2b) = operator) /\ ((length n2b) = 3%nat)) -> True -> ((v = ((1%F :: (eq :: (lt :: (gt :: (_in :: ((1%F - _in)%F :: (0%F :: (0%F :: nil))))))))!(^ (as_le_f n2b)))) -> (((operator = 0%F) -> (v = 1%F)) /\ (~((operator = 0%F)) -> (((operator = 1%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (_in = (value!0%nat))) /\ ((v = 0%F) -> ~(_in = (value!0%nat)))))) /\ (~((operator = 1%F)) -> (((operator = 2%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((^ _in) < (^ (value!0%nat)))) /\ ((v = 0%F) -> ~((^ _in) < (^ (value!0%nat))))))) /\ (~((operator = 2%F)) -> (((operator = 3%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((^ (value!0%nat)) < (^ _in))) /\ ((v = 0%F) -> ~((^ (value!0%nat)) < (^ _in)))))) /\ (~((operator = 3%F)) -> (((operator = 4%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (exists (j:nat), 0%nat <= j < valueArraySize -> ((value!j) = _in))) /\ ((v = 0%F) -> ~((exists (j:nat), 0%nat <= j < valueArraySize -> ((value!j) = _in))))))) /\ (~((operator = 4%F)) -> (((operator = 5%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ~((exists (j:nat), 0%nat <= j < valueArraySize -> ((value!j) = _in)))) /\ ((v = 0%F) -> ~(~((exists (j:nat), 0%nat <= j < valueArraySize -> ((value!j) = _in)))))))) /\ (~((operator = 5%F)) -> False))))))))))))).
Proof. Admitted.

(** ** getValueByIndex *)

(* print_endline (generate_lemmas get_val_by_idx (typecheck_circuit (add_to_deltas d_empty [num2bits; mux3]) get_val_by_idx));; *)

(* TODO *)

(** ** getIdenState *)

(* print_endline (generate_lemmas get_iden_state (typecheck_circuit (add_to_delta d_empty poseidon) get_iden_state));; *)

(* TODO *)

(** ** cutId *)

(* print_endline (generate_lemmas cut_id (typecheck_circuit (add_to_deltas d_empty [num2bits; bits2num]) cut_id));; *)

(* TODO *)

(** ** cutState *)

(* print_endline (generate_lemmas cut_st (typecheck_circuit (add_to_deltas d_empty [num2bits; bits2num]) cut_st));; *)

(* TODO *)
