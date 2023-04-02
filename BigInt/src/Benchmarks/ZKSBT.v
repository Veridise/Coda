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

(* TODO *)

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
