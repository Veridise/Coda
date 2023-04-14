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

From Circom Require Import Circom Util Default Tuple ListUtil LibTactics Signed Simplify Repr Coda.
From Circom.CircomLib Require Import Bitify.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.
Local Coercion Z.to_nat : Z >-> nat.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Notation "3" := (1 + 1 + 1)%F.
Notation "4" := (1 + 1 + 1 + 1)%F.
Notation "5" := (1 + 1 + 1 + 1 + 1)%F.

Definition Poseidon (nInputs : nat) (inputs : list F) : F. Admitted.

Axiom Poseidon_3 : forall inputs : list F,
  length inputs = 3%nat ->
  Poseidon 3%nat inputs = Poseidon 3%nat ((inputs!0%nat)::(inputs!1%nat)::(inputs!3%nat)::nil).

#[global]Hint Extern 10 (Forall _ (firstn _ _)) => apply Forall_firstn: core.
#[global]Hint Extern 10  => match goal with
   | [ |- context[List_nth_Default _ _] ] => unfold_default end: core.
   #[global]Hint Extern 10  => match goal with
   | [ |- context[List.nth  _ _ _] ] => apply Forall_nth end: core.
#[global]Hint Extern 10 => match goal with
  [ |- context[length _] ] => rewrite_length end: core.
#[global]Hint Extern 10 (Forall _ (skipn _ _)) => apply Forall_skipn: core.

#[global]Hint Extern 10 (Forall _ (_ :: _)) => constructor: core.
#[global]Hint Extern 10 (Z.of_N (N.of_nat _)) => rewrite nat_N_Z: core.
#[global]Hint Extern 10  => repeat match goal with
  [ H: context[Z.of_N (N.of_nat _)] |- _] => rewrite nat_N_Z in H end: core.

#[global]Hint Extern 10 (_ < _) => lia: core.
#[global]Hint Extern 10 (_ < _)%nat => lia: core.
#[global]Hint Extern 10 (_ <= _) => lia: core.
#[global]Hint Extern 10 (_ <= _)%nat => lia: core.
#[global]Hint Extern 10 (_ > _) => lia: core.
#[global]Hint Extern 10 (_ > _)%nat => lia: core.
#[global]Hint Extern 10 (_ >= _) => lia: core.
#[global]Hint Extern 10 (_ >= _)%nat => lia: core.
#[global]Hint Extern 10 (S _ = S _) => f_equal: core.

(** ** IN *)

Definition sum_occur i (value : list F) (v : F) : F :=
  fold_left (fun acc (x:F) => if (dec (x = v))%F then (1 + acc)%F else acc) (firstn i value) 0%F.

Lemma sum_occur_max: forall (value : list F) (v : F),
  (sum_occur (length value) value v <=z length value).
Proof.
  unfold sum_occur. induction value;simpl;intros;try easy.
  destruct (dec (a = v))%F; subst.
Admitted.

Lemma sum_occur_nonneg: forall (value : list F) (v : F),
  (exists i : nat,
        0 <= i < length value -> value ! i = v) <->
  (0 < ^ sum_occur (length value) value v).
Proof.
Admitted.

Lemma IN_obligation0_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (v : Z), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> True -> Forall (fun x1 => True) value -> ((length value) = valueArraySize) -> True -> ((v = 0%nat) -> True).
Proof. hammer. Qed.

Lemma IN_obligation1_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (v : nat), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> True -> Forall (fun x2 => True) value -> ((length value) = valueArraySize) -> ((((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < v) /\ ((v < (2%nat ^ 252%nat)%Z) /\ True)))) /\ (v = valueArraySize)) -> True).
Proof. hammer. Qed.

Lemma IN_obligation2_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (v : Z), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> True -> Forall (fun x3 => True) value -> ((length value) = valueArraySize) -> True -> ((0%nat <= v) -> True).
Proof. hammer. Qed.

Lemma IN_obligation3_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (v : Z), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> True -> Forall (fun x4 => True) value -> ((length value) = valueArraySize) -> True -> (((0%nat <= v) /\ (v < valueArraySize)) -> True).
Proof. hammer. Qed.

Lemma IN_obligation4_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (i : nat) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> True -> Forall (fun x5 => True) value -> ((length value) = valueArraySize) -> (i < valueArraySize) -> True -> ((v = (sum_occur i value _in)) -> True).
Proof. hammer. Qed.

Lemma IN_obligation5_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (i : nat) (x : F) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> True -> Forall (fun x6 => True) value -> ((length value) = valueArraySize) -> (i < valueArraySize) -> (x = (sum_occur i value _in)) -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma IN_obligation6_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (i : nat) (x : F) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> True -> Forall (fun x7 => True) value -> ((length value) = valueArraySize) -> (i < valueArraySize) -> (x = (sum_occur i value _in)) -> True -> ((v = (value!i)) -> True).
Proof. hammer. Qed.

Lemma IN_obligation7_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (i : nat) (x : F) (ise_u : (F * F)) (u : F) (ise : F) (_u0 : (F * F)) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> True -> Forall (fun x8 => True) value -> ((length value) = valueArraySize) -> (i < valueArraySize) -> (x = (sum_occur i value _in)) -> match ise_u with (x9,x10) => (((x9 = 0%F) \/ (x9 = 1%F)) /\ (((x9 = 1%F) -> (_in = (value!i))) /\ ((x9 = 0%F) -> ~(_in = (value!i))))) end -> match ise_u with (x9,x10) => (x10 = 1%F) end -> match ise_u with (x9,x10) => True end -> ((u = 1%F) /\ (u = (snd ise_u))) -> ((((ise = 0%F) \/ (ise = 1%F)) /\ (((ise = 1%F) -> (_in = (value!i))) /\ ((ise = 0%F) -> ~(_in = (value!i))))) /\ (ise = (fst ise_u))) -> match _u0 with (x11,x12) => True end -> match _u0 with (x11,x12) => True end -> match _u0 with (x11,x12) => (ise_u = ise_u) end -> True -> (((v = (sum_occur i value _in)) /\ (v = x)) -> True).
Proof. hammer. Qed.

Lemma IN_obligation8_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (i : nat) (x : F) (ise_u : (F * F)) (u : F) (ise : F) (_u0 : (F * F)) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> True -> Forall (fun x13 => True) value -> ((length value) = valueArraySize) -> (i < valueArraySize) -> (x = (sum_occur i value _in)) -> match ise_u with (x14,x15) => (((x14 = 0%F) \/ (x14 = 1%F)) /\ (((x14 = 1%F) -> (_in = (value!i))) /\ ((x14 = 0%F) -> ~(_in = (value!i))))) end -> match ise_u with (x14,x15) => (x15 = 1%F) end -> match ise_u with (x14,x15) => True end -> ((u = 1%F) /\ (u = (snd ise_u))) -> ((((ise = 0%F) \/ (ise = 1%F)) /\ (((ise = 1%F) -> (_in = (value!i))) /\ ((ise = 0%F) -> ~(_in = (value!i))))) /\ (ise = (fst ise_u))) -> match _u0 with (x16,x17) => True end -> match _u0 with (x16,x17) => True end -> match _u0 with (x16,x17) => (ise_u = ise_u) end -> True -> ((((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (_in = (value!i))) /\ ((v = 0%F) -> ~(_in = (value!i))))) /\ (v = (fst ise_u))) /\ (v = ise)) -> True).
Proof. hammer. Qed.

Lemma IN_obligation9: forall (valueArraySize : nat) (_in : F) (value : (list F)) (i : nat) (x : F) (ise_u : (F * F)) (u : F) (ise : F) (_u0 : (F * F)) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> True -> Forall (fun x18 => True) value -> ((length value) = valueArraySize) -> (i < valueArraySize) -> (x = (sum_occur i value _in)) -> match ise_u with (x19,x20) => (((x19 = 0%F) \/ (x19 = 1%F)) /\ (((x19 = 1%F) -> (_in = (value!i))) /\ ((x19 = 0%F) -> ~(_in = (value!i))))) end -> match ise_u with (x19,x20) => (x20 = 1%F) end -> match ise_u with (x19,x20) => True end -> ((u = 1%F) /\ (u = (snd ise_u))) -> ((((ise = 0%F) \/ (ise = 1%F)) /\ (((ise = 1%F) -> (_in = (value!i))) /\ ((ise = 0%F) -> ~(_in = (value!i))))) /\ (ise = (fst ise_u))) -> match _u0 with (x21,x22) => True end -> match _u0 with (x21,x22) => True end -> match _u0 with (x21,x22) => (ise_u = ise_u) end -> True -> ((v = (x + ise)%F) -> (v = (sum_occur (i + 1%nat)%nat value _in))).
Proof.
intros. destruct ise_u;simpl in *;try easy.
unwrap_C; intuition; subst; try fqsatz;try (left; fqsatz); try (right; fqsatz).
- unfold sum_occur. replace (i+1)%nat with (S i) by lia. 
  rewrite fold_left_firstn_S';try lia.
  destruct dec;try fqsatz. exfalso. apply H17;auto.
- unfold sum_occur. replace (i+1)%nat with (S i) by lia. 
  rewrite fold_left_firstn_S';try lia.
  destruct dec;try fqsatz. 
Qed.

Lemma IN_obligation10: forall (valueArraySize : nat) (_in : F) (value : (list F)) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> True -> Forall (fun x23 => True) value -> ((length value) = valueArraySize) -> True -> ((v = 0%F) -> (v = (sum_occur 0%nat value _in))).
Proof. intuit; subst; Signed.solve_to_Z. Qed.

Lemma IN_obligation11: forall (valueArraySize : nat) (_in : F) (value : (list F)) (count : F) (v : Z), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> True -> Forall (fun x24 => True) value -> ((length value) = valueArraySize) -> (count = (sum_occur valueArraySize value _in)) -> True -> ((v = 252%nat) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof. hammer. Qed.

Lemma IN_obligation12: forall (valueArraySize : nat) (_in : F) (value : (list F)) (count : F) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> True -> Forall (fun x25 => True) value -> ((length value) = valueArraySize) -> (count = (sum_occur valueArraySize value _in)) -> True -> (((v = (sum_occur valueArraySize value _in)) /\ (v = count)) -> ((^ v) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z)).
Proof.
  unwrap_C;intuit; subst; Signed.solve_to_Z.
  rewrite sum_occur_max; Signed.solve_to_Z.
Qed.

Lemma IN_obligation13: forall (valueArraySize : nat) (_in : F) (value : (list F)) (count : F) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> True -> Forall (fun x26 => True) value -> ((length value) = valueArraySize) -> (count = (sum_occur valueArraySize value _in)) -> True -> ((v = 0%F) -> ((^ v) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z)).
Proof. intuit; subst; Signed.solve_to_Z. Qed.

Lemma IN_obligation14: forall (valueArraySize : nat) (_in : F) (value : (list F)) (count : F) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> True -> Forall (fun x27 => True) value -> ((length value) = valueArraySize) -> (count = (sum_occur valueArraySize value _in)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((^ 0%F) < (^ count))) /\ ((v = 0%F) -> ~((^ 0%F) < (^ count))))) -> (((1%nat <= (^ v)) -> (exists (i:nat), 0%nat <= i < valueArraySize -> ((value!i) = _in))) /\ ((v = 0%F) -> ~((exists (i:nat), 0%nat <= i < valueArraySize -> ((value!i) = _in)))))).
Proof.
  intuit; subst; Signed.solve_to_Z;try easy.
  - apply sum_occur_nonneg in H13;auto.
  - apply sum_occur_nonneg;auto.
Qed.

(** ** Query *)

Local Hint Resolve q_3 q_4 q_5 : q.

Lemma Query_obligation0_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (operator : F) (x : F) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> ((^ _in) < (2%nat ^ 252%nat)%Z) -> Forall (fun x28 => True) value -> (((^ (value!0%nat)) < (2%nat ^ 252%nat)%Z) /\ ((length value) = valueArraySize)) -> True -> (x = (value!0%nat)) -> True -> ((((^ v) < (2%nat ^ 252%nat)%Z) /\ (v = _in)) -> True).
Proof. hammer. Qed.

Lemma Query_obligation1_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (operator : F) (x : F) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> ((^ _in) < (2%nat ^ 252%nat)%Z) -> Forall (fun x29 => True) value -> (((^ (value!0%nat)) < (2%nat ^ 252%nat)%Z) /\ ((length value) = valueArraySize)) -> True -> (x = (value!0%nat)) -> True -> (((v = (value!0%nat)) /\ (v = x)) -> True).
Proof. hammer. Qed.

Lemma Query_obligation2: forall (valueArraySize : nat) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (v : Z), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> ((^ _in) < (2%nat ^ 252%nat)%Z) -> Forall (fun x30 => True) value -> (((^ (value!0%nat)) < (2%nat ^ 252%nat)%Z) /\ ((length value) = valueArraySize)) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> True -> ((v = 252%nat) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof. hammer. Qed.

Lemma Query_obligation3: forall (valueArraySize : nat) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> ((^ _in) < (2%nat ^ 252%nat)%Z) -> Forall (fun x31 => True) value -> (((^ (value!0%nat)) < (2%nat ^ 252%nat)%Z) /\ ((length value) = valueArraySize)) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> True -> ((((^ v) < (2%nat ^ 252%nat)%Z) /\ (v = _in)) -> ((^ v) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z)).
Proof. hammer. Qed.

Lemma Query_obligation4: forall (valueArraySize : nat) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> ((^ _in) < (2%nat ^ 252%nat)%Z) -> Forall (fun x32 => True) value -> (((^ (value!0%nat)) < (2%nat ^ 252%nat)%Z) /\ ((length value) = valueArraySize)) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> True -> (((v = (value!0%nat)) /\ (v = x)) -> ((^ v) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z)).
Proof. hammer. Qed.

Lemma Query_obligation5: forall (valueArraySize : nat) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (v : Z), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> ((^ _in) < (2%nat ^ 252%nat)%Z) -> Forall (fun x33 => True) value -> (((^ (value!0%nat)) < (2%nat ^ 252%nat)%Z) /\ ((length value) = valueArraySize)) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> True -> ((v = 252%nat) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof. hammer. Qed.

Lemma Query_obligation6: forall (valueArraySize : nat) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> ((^ _in) < (2%nat ^ 252%nat)%Z) -> Forall (fun x34 => True) value -> (((^ (value!0%nat)) < (2%nat ^ 252%nat)%Z) /\ ((length value) = valueArraySize)) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> True -> ((((^ v) < (2%nat ^ 252%nat)%Z) /\ (v = _in)) -> ((^ v) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z)).
Proof. hammer. Qed.

Lemma Query_obligation7: forall (valueArraySize : nat) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> ((^ _in) < (2%nat ^ 252%nat)%Z) -> Forall (fun x35 => True) value -> (((^ (value!0%nat)) < (2%nat ^ 252%nat)%Z) /\ ((length value) = valueArraySize)) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> True -> (((v = (value!0%nat)) /\ (v = x)) -> ((^ v) <= ((2%nat ^ 252%nat)%Z - 1%nat)%Z)).
Proof. hammer. Qed.

Lemma Query_obligation8: forall (valueArraySize : nat) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (gt : F) (v : nat), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> ((^ _in) < (2%nat ^ 252%nat)%Z) -> Forall (fun x36 => True) value -> (((^ (value!0%nat)) < (2%nat ^ 252%nat)%Z) /\ ((length value) = valueArraySize)) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ x) < (^ _in))) /\ ((gt = 0%F) -> ~((^ x) < (^ _in))))) -> ((((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < v) /\ ((v < (2%nat ^ 252%nat)%Z) /\ True)))) /\ (v = valueArraySize)) -> ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < v) /\ ((v < (2%nat ^ 252%nat)%Z) /\ True))))).
Proof. hammer. Qed.

Lemma Query_obligation9: forall (valueArraySize : nat) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (gt : F) (v : Z), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> ((^ _in) < (2%nat ^ 252%nat)%Z) -> Forall (fun x37 => True) value -> (((^ (value!0%nat)) < (2%nat ^ 252%nat)%Z) /\ ((length value) = valueArraySize)) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ x) < (^ _in))) /\ ((gt = 0%F) -> ~((^ x) < (^ _in))))) -> True -> ((0%nat <= v) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma Query_obligation10_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (gt : F) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> ((^ _in) < (2%nat ^ 252%nat)%Z) -> Forall (fun x38 => True) value -> (((^ (value!0%nat)) < (2%nat ^ 252%nat)%Z) /\ ((length value) = valueArraySize)) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ x) < (^ _in))) /\ ((gt = 0%F) -> ~((^ x) < (^ _in))))) -> True -> ((((^ v) < (2%nat ^ 252%nat)%Z) /\ (v = _in)) -> True).
Proof. hammer. Qed.

Lemma Query_obligation11: forall (valueArraySize : nat) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (gt : F) (v : (list F)), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> ((^ _in) < (2%nat ^ 252%nat)%Z) -> Forall (fun x39 => True) value -> (((^ (value!0%nat)) < (2%nat ^ 252%nat)%Z) /\ ((length value) = valueArraySize)) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ x) < (^ _in))) /\ ((gt = 0%F) -> ~((^ x) < (^ _in))))) -> Forall (fun x40 => True) v -> True -> (((((^ (v!0%nat)) < (2%nat ^ 252%nat)%Z) /\ ((length v) = valueArraySize)) /\ (v = value)) -> ((length v) = valueArraySize)).
Proof. hammer. Qed.

Lemma Query_obligation12: forall (valueArraySize : nat) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (gt : F) (_in : F) (v : Z), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> ((^ _in) < (2%nat ^ 252%nat)%Z) -> Forall (fun x41 => True) value -> (((^ (value!0%nat)) < (2%nat ^ 252%nat)%Z) /\ ((length value) = valueArraySize)) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ x) < (^ _in))) /\ ((gt = 0%F) -> ~((^ x) < (^ _in))))) -> (((1%nat <= (^ _in)) -> (exists (i:nat), 0%nat <= i < valueArraySize -> ((value!i) = _in))) /\ ((_in = 0%F) -> ~((exists (i:nat), 0%nat <= i < valueArraySize -> ((value!i) = _in))))) -> True -> ((v = 3%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma Query_obligation13_trivial: forall (valueArraySize : nat) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (gt : F) (_in : F) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> ((^ _in) < (2%nat ^ 252%nat)%Z) -> Forall (fun x42 => True) value -> (((^ (value!0%nat)) < (2%nat ^ 252%nat)%Z) /\ ((length value) = valueArraySize)) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ x) < (^ _in))) /\ ((gt = 0%F) -> ~((^ x) < (^ _in))))) -> (((1%nat <= (^ _in)) -> (exists (i:nat), 0%nat <= i < valueArraySize -> ((value!i) = _in))) /\ ((_in = 0%F) -> ~((exists (i:nat), 0%nat <= i < valueArraySize -> ((value!i) = _in))))) -> True -> ((v = operator) -> True).
Proof. hammer. Qed.

Lemma Query_obligation14: forall (valueArraySize : nat) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (gt : F) (_in : F) (n2b : (list F)) (v : (list F)), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> ((^ _in) < (2%nat ^ 252%nat)%Z) -> Forall (fun x43 => True) value -> (((^ (value!0%nat)) < (2%nat ^ 252%nat)%Z) /\ ((length value) = valueArraySize)) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ x) < (^ _in))) /\ ((gt = 0%F) -> ~((^ x) < (^ _in))))) -> (((1%nat <= (^ _in)) -> (exists (i:nat), 0%nat <= i < valueArraySize -> ((value!i) = _in))) /\ ((_in = 0%F) -> ~((exists (i:nat), 0%nat <= i < valueArraySize -> ((value!i) = _in))))) -> Forall (fun x44 => ((x44 = 0%F) \/ (x44 = 1%F))) n2b -> (((as_le_f n2b) = operator) /\ ((length n2b) = 3%nat)) -> Forall (fun x45 => True) v -> True -> ((((((((((True /\ ((v!0%nat) = 1%F)) /\ ((v!1%nat) = eq)) /\ ((v!2%nat) = lt)) /\ ((v!3%nat) = gt)) /\ ((v!4%nat) = _in)) /\ ((v!5%nat) = (1%F - _in)%F)) /\ ((v!6%nat) = 0%F)) /\ ((v!7%nat) = 0%F)) /\ ((length v) = 8%nat)) -> ((length v) = 8%nat)).
Proof. hammer. Qed.

Lemma Query_obligation15: forall (valueArraySize : nat) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (gt : F) (_in : F) (n2b : (list F)) (v : (list F)), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> ((^ _in) < (2%nat ^ 252%nat)%Z) -> Forall (fun x46 => True) value -> (((^ (value!0%nat)) < (2%nat ^ 252%nat)%Z) /\ ((length value) = valueArraySize)) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ x) < (^ _in))) /\ ((gt = 0%F) -> ~((^ x) < (^ _in))))) -> (((1%nat <= (^ _in)) -> (exists (i:nat), 0%nat <= i < valueArraySize -> ((value!i) = _in))) /\ ((_in = 0%F) -> ~((exists (i:nat), 0%nat <= i < valueArraySize -> ((value!i) = _in))))) -> Forall (fun x47 => ((x47 = 0%F) \/ (x47 = 1%F))) n2b -> (((as_le_f n2b) = operator) /\ ((length n2b) = 3%nat)) -> Forall (fun x48 => ((x48 = 0%F) \/ (x48 = 1%F))) v -> True -> (((((as_le_f v) = operator) /\ ((length v) = 3%nat)) /\ (v = n2b)) -> ((length v) = 3%nat)).
Proof. hammer. Qed.

Lemma Query_obligation16: forall (valueArraySize : nat) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (gt : F) (_in : F) (n2b : (list F)) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> ((^ _in) < (2%nat ^ 252%nat)%Z) -> Forall (fun x49 => True) value -> (((^ (value!0%nat)) < (2%nat ^ 252%nat)%Z) /\ ((length value) = valueArraySize)) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ x) < (^ _in))) /\ ((gt = 0%F) -> ~((^ x) < (^ _in))))) -> (((1%nat <= (^ _in)) -> (exists (i:nat), 0%nat <= i < valueArraySize -> ((value!i) = _in))) /\ ((_in = 0%F) -> ~((exists (i:nat), 0%nat <= i < valueArraySize -> ((value!i) = _in))))) -> Forall (fun x50 => ((x50 = 0%F) \/ (x50 = 1%F))) n2b -> (((as_le_f n2b) = operator) /\ ((length n2b) = 3%nat)) -> True -> (((v = 0%F) \/ (v = 1%F)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma Query_obligation17: forall (valueArraySize : nat) (_in : F) (value : (list F)) (operator : F) (x : F) (eq : F) (lt : F) (gt : F) (_in : F) (n2b : (list F)) (v : F), ((2%nat < C.q) /\ ((252%nat <= (C.k - 1%nat)%Z) /\ ((0%nat < valueArraySize) /\ ((valueArraySize < (2%nat ^ 252%nat)%Z) /\ True)))) -> ((^ _in) < (2%nat ^ 252%nat)%Z) -> Forall (fun x51 => True) value -> (((^ (value!0%nat)) < (2%nat ^ 252%nat)%Z) /\ ((length value) = valueArraySize)) -> True -> (x = (value!0%nat)) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (_in = x)) /\ ((eq = 0%F) -> ~(_in = x)))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ _in) < (^ x))) /\ ((lt = 0%F) -> ~((^ _in) < (^ x))))) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ x) < (^ _in))) /\ ((gt = 0%F) -> ~((^ x) < (^ _in))))) -> (((1%nat <= (^ _in)) -> (exists (i:nat), 0%nat <= i < valueArraySize -> ((value!i) = _in))) /\ ((_in = 0%F) -> ~((exists (i:nat), 0%nat <= i < valueArraySize -> ((value!i) = _in))))) -> Forall (fun x52 => ((x52 = 0%F) \/ (x52 = 1%F))) n2b -> (((as_le_f n2b) = operator) /\ ((length n2b) = 3%nat)) -> True -> ((v = ((1%F :: (eq :: (lt :: (gt :: (_in :: ((1%F - _in)%F :: (0%F :: (0%F :: nil))))))))!(^ (as_le_f n2b)))) -> (((operator = 0%F) -> (v = 1%F)) /\ (~((operator = 0%F)) -> (((operator = 1%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (_in = (value!0%nat))) /\ ((v = 0%F) -> ~(_in = (value!0%nat)))))) /\ (~((operator = 1%F)) -> (((operator = 2%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((^ _in) < (^ (value!0%nat)))) /\ ((v = 0%F) -> ~((^ _in) < (^ (value!0%nat))))))) /\ (~((operator = 2%F)) -> (((operator = 3%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((^ (value!0%nat)) < (^ _in))) /\ ((v = 0%F) -> ~((^ (value!0%nat)) < (^ _in)))))) /\ (~((operator = 3%F)) -> (((operator = 4%F) -> (((1%nat <= (^ v)) -> (exists (j:nat), 0%nat <= j < valueArraySize -> ((value!j) = _in))) /\ ((v = 0%F) -> ~((exists (j:nat), 0%nat <= j < valueArraySize -> ((value!j) = _in)))))) /\ (~((operator = 4%F)) -> (((operator = 5%F) -> (((1%nat <= (^ v)) -> ~((exists (j:nat), 0%nat <= j < valueArraySize -> ((value!j) = _in)))) /\ ((v = 0%F) -> ~(~((exists (j:nat), 0%nat <= j < valueArraySize -> ((value!j) = _in))))))) /\ (~((operator = 5%F)) -> True))))))))))))).
Proof. 
  unwrap_C; intros; repeat split.
  - intros. subst. inversion H10. rewrite H4. simpl. auto.
  - subst. inversion H10. rewrite H4. Signed.solve_to_Z. inversion H5. auto.
  - intros. subst. inversion H10. rewrite H4 in *. 
    assert (eq = 1)%F. rewrite <- H15.  Signed.solve_to_Z. auto.
    subst. inversion H5. intuit.
  - intros. subst. inversion H10. rewrite H4 in *. 
    assert (eq = 0)%F. rewrite <- H15.  Signed.solve_to_Z. auto.
    subst. inversion H5. intuition.
  - intros. subst. inversion H10. rewrite H4 in *. Signed.solve_to_Z. inversion H6. auto.
  - intros. subst. inversion H10. rewrite H4 in *.
    assert (lt = 1)%F. rewrite <- H16.  Signed.solve_to_Z. auto.
    subst. inversion H6. intuition.
  - intros. subst. inversion H10. rewrite H4 in *.
    assert (lt = 0)%F. rewrite <- H16.  Signed.solve_to_Z. auto.
    subst. inversion H6. intuition.
  - intros. subst. inversion H10. rewrite H4 in *. Signed.solve_to_Z;try fqsatz. inversion H7. auto.
    split;try lia. destruct H as [? [?]]. auto with q.
  - intros. subst. inversion H10. rewrite H4 in *.
    assert (gt = 1)%F. rewrite <- H17.  Signed.solve_to_Z. auto. auto with q.
    subst. inversion H7. intuition.
  - intros. subst. inversion H10. rewrite H4 in *.
    assert (gt = 0)%F. rewrite <- H17.  Signed.solve_to_Z;auto with q. 
    subst. inversion H7. intuition.
  - intros. subst. inversion H10. rewrite H4 in *. Signed.solve_to_Z;try fqsatz. 
    inversion H8. apply H17. rewrite H18. Signed.solve_to_Z;auto with q.
    assert((1:: eq:: lt :: gt :: _in0 :: (1 - _in0)%F :: 0 :: 0 :: nil)%F ! (1 + 1 + 1 + 1)%Z = _in0). auto. rewrite H20. auto.
  - intros. subst. inversion H10. rewrite H4 in *. 
    assert (_in0 = 0)%F. rewrite <- H18.  Signed.solve_to_Z;auto with q. 
    subst. inversion H8. intuition.
  - intros. subst. inversion H10. rewrite H4 in *. 
    inversion H8. apply H20.  
    assert (1%nat <= ^(1 - _in0)%F)%F. remember (1 - _in0)%F as x. 
    rewrite H19. Signed.solve_to_Z;auto with q. easy.
    apply leq_minus;auto.
  - intros. subst. inversion H10. rewrite H4 in *. 
    assert ((1 - _in0) = 0)%F. rewrite <- H19.  Signed.solve_to_Z; auto with q.
    subst. inversion H8. assert (_in0 = 1)%F. fqsatz. intro. apply H23.
    apply H20. rewrite H22. Signed.solve_to_Z.
Qed.

(** ** getValueByIndex *)

Lemma getValueByIndex_obligation0: forall (claim : (list F)) (index : F) (v : Z), Forall (fun x0 => True) claim -> ((length claim) = 8%nat) -> True -> True -> ((v = 8%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma getValueByIndex_obligation1_trivial: forall (claim : (list F)) (index : F) (v : F), Forall (fun x1 => True) claim -> ((length claim) = 8%nat) -> True -> True -> ((v = index) -> True).
Proof. hammer. Qed.

Lemma getValueByIndex_obligation2_trivial: forall (claim : (list F)) (index : F) (n2b : (list F)) (v : Z), Forall (fun x2 => True) claim -> ((length claim) = 8%nat) -> True -> Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) n2b -> (((as_le_f n2b) = index) /\ ((length n2b) = 8%nat)) -> True -> ((v = 3%nat) -> True).
Proof. hammer. Qed.

Lemma getValueByIndex_obligation3: forall (claim : (list F)) (index : F) (n2b : (list F)) (z : (list F)) (v : (list F)), Forall (fun x4 => True) claim -> ((length claim) = 8%nat) -> True -> Forall (fun x5 => ((x5 = 0%F) \/ (x5 = 1%F))) n2b -> (((as_le_f n2b) = index) /\ ((length n2b) = 8%nat)) -> Forall (fun x6 => ((x6 = 0%F) \/ (x6 = 1%F))) z -> ((z = (n2b[:3%nat])) /\ ((length z) = 3%nat)) -> Forall (fun x7 => True) v -> True -> ((((length v) = 8%nat) /\ (v = claim)) -> ((length v) = 8%nat)).
Proof. hammer. Qed.

Lemma getValueByIndex_obligation4: forall (claim : (list F)) (index : F) (n2b : (list F)) (z : (list F)) (v : (list F)), Forall (fun x8 => True) claim -> ((length claim) = 8%nat) -> True -> Forall (fun x9 => ((x9 = 0%F) \/ (x9 = 1%F))) n2b -> (((as_le_f n2b) = index) /\ ((length n2b) = 8%nat)) -> Forall (fun x10 => ((x10 = 0%F) \/ (x10 = 1%F))) z -> ((z = (n2b[:3%nat])) /\ ((length z) = 3%nat)) -> Forall (fun x11 => ((x11 = 0%F) \/ (x11 = 1%F))) v -> True -> ((((v = (n2b[:3%nat])) /\ ((length v) = 3%nat)) /\ (v = z)) -> ((length v) = 3%nat)).
Proof. hammer. Qed.

Lemma getValueByIndex_obligation5: forall (claim : (list F)) (index : F) (n2b : (list F)) (z : (list F)) (v : F), Forall (fun x12 => True) claim -> ((length claim) = 8%nat) -> True -> Forall (fun x13 => ((x13 = 0%F) \/ (x13 = 1%F))) n2b -> (((as_le_f n2b) = index) /\ ((length n2b) = 8%nat)) -> Forall (fun x14 => ((x14 = 0%F) \/ (x14 = 1%F))) z -> ((z = (n2b[:3%nat])) /\ ((length z) = 3%nat)) -> True -> (((v = 0%F) \/ (v = 1%F)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma getValueByIndex_obligation6: forall (claim : (list F)) (index : F) (n2b : (list F)) (z : (list F)) (v : F), Forall (fun x15 => True) claim -> ((length claim) = 8%nat) -> True -> Forall (fun x16 => ((x16 = 0%F) \/ (x16 = 1%F))) n2b -> (((as_le_f n2b) = index) /\ ((length n2b) = 8%nat)) -> Forall (fun x17 => ((x17 = 0%F) \/ (x17 = 1%F))) z -> ((z = (n2b[:3%nat])) /\ ((length z) = 3%nat)) -> True -> ((v = (claim!(^ (as_le_f z)))) -> (v = (claim!((^ index) mod 8%nat)%Z))).
Proof. intuit. subst. simpl in *; subst. Admitted.

(** ** getIdenState *)

Lemma getIdenState_obligation0: forall (claimsTreeRoot : F) (revTreeRoot : F) (rootsTreeRoot : F) (v : Z), True -> True -> True -> True -> ((v = 3%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma getIdenState_obligation1: forall (claimsTreeRoot : F) (revTreeRoot : F) (rootsTreeRoot : F) (v : (list F)), True -> True -> True -> Forall (fun x48 => True) v -> True -> (((((True /\ ((v!0%nat) = claimsTreeRoot)) /\ ((v!1%nat) = revTreeRoot)) /\ ((v!2%nat) = rootsTreeRoot)) /\ ((length v) = 3%nat)) -> ((length v) = 3%nat)).
Proof. hammer. Qed.

Lemma getIdenState_obligation2: forall (claimsTreeRoot : F) (revTreeRoot : F) (rootsTreeRoot : F) (v : F), True -> True -> True -> True -> ((v = (Poseidon 3%nat (claimsTreeRoot :: (revTreeRoot :: (rootsTreeRoot :: nil))))) -> (v = (Poseidon 3%nat (claimsTreeRoot :: (revTreeRoot :: (rootsTreeRoot :: nil)))))).
Proof. hammer. Qed.

(** ** cutId *)

Lemma cutId_obligation0: forall (_in : F) (v : Z), True -> True -> ((v = 256%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma cutId_obligation1_trivial: forall (_in : F) (v : F), True -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma cutId_obligation2_trivial: forall (_in : F) (n2b : (list F)) (v : Z), True -> Forall (fun x0 => ((x0 = 0%F) \/ (x0 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 256%nat)) -> True -> ((v = 16%nat) -> True).
Proof. hammer. Qed.

Lemma cutId_obligation3_trivial: forall (_in : F) (n2b : (list F)) (d : (list F)) (v : Z), True -> Forall (fun x1 => ((x1 = 0%F) \/ (x1 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 256%nat)) -> Forall (fun x2 => ((x2 = 0%F) \/ (x2 = 1%F))) d -> ((d = (skipn 16%nat n2b)) /\ ((length d) = ((length n2b) - 16%nat)%nat)) -> True -> ((v = 216%nat) -> True).
Proof. hammer. Qed.

Lemma cutId_obligation4: forall (_in : F) (n2b : (list F)) (d : (list F)) (t : (list F)) (v : Z), True -> Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 256%nat)) -> Forall (fun x4 => ((x4 = 0%F) \/ (x4 = 1%F))) d -> ((d = (skipn 16%nat n2b)) /\ ((length d) = ((length n2b) - 16%nat)%nat)) -> Forall (fun x5 => ((x5 = 0%F) \/ (x5 = 1%F))) t -> ((t = (d[:216%nat])) /\ ((length t) = 216%nat)) -> True -> ((v = 216%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma cutId_obligation5: forall (_in : F) (n2b : (list F)) (d : (list F)) (t : (list F)) (v : (list F)), True -> Forall (fun x6 => ((x6 = 0%F) \/ (x6 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 256%nat)) -> Forall (fun x7 => ((x7 = 0%F) \/ (x7 = 1%F))) d -> ((d = (skipn 16%nat n2b)) /\ ((length d) = ((length n2b) - 16%nat)%nat)) -> Forall (fun x8 => ((x8 = 0%F) \/ (x8 = 1%F))) t -> ((t = (d[:216%nat])) /\ ((length t) = 216%nat)) -> Forall (fun x9 => ((x9 = 0%F) \/ (x9 = 1%F))) v -> True -> ((((v = (d[:216%nat])) /\ ((length v) = 216%nat)) /\ (v = t)) -> ((length v) = 216%nat)).
Proof. hammer. Qed.

Lemma cutId_obligation6: forall (_in : F) (n2b : (list F)) (d : (list F)) (t : (list F)) (v : F), True -> Forall (fun x10 => ((x10 = 0%F) \/ (x10 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 256%nat)) -> Forall (fun x11 => ((x11 = 0%F) \/ (x11 = 1%F))) d -> ((d = (skipn 16%nat n2b)) /\ ((length d) = ((length n2b) - 16%nat)%nat)) -> Forall (fun x12 => ((x12 = 0%F) \/ (x12 = 1%F))) t -> ((t = (d[:216%nat])) /\ ((length t) = 216%nat)) -> True -> (((v = 0%F) \/ (v = 1%F)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma cutId_obligation7: forall (_in : F) (n2b : (list F)) (d : (list F)) (t : (list F)) (v : F), True -> Forall (fun x13 => ((x13 = 0%F) \/ (x13 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 256%nat)) -> Forall (fun x14 => ((x14 = 0%F) \/ (x14 = 1%F))) d -> ((d = (skipn 16%nat n2b)) /\ ((length d) = ((length n2b) - 16%nat)%nat)) -> Forall (fun x15 => ((x15 = 0%F) \/ (x15 = 1%F))) t -> ((t = (d[:216%nat])) /\ ((length t) = 216%nat)) -> True -> ((v = (as_le_f t)) -> (v = (as_le_f (take 216%nat (drop 16%nat (to_le_f 256%nat _in)))))).
Proof. 
  intuit. subst. f_equal. unfold take. f_equal. unfold drop. f_equal. rewrite <- H9.
  rewrite <- to_le_f_as_le_f;auto. 
Qed.

(** ** cutState *)
Lemma cutState_obligation0: forall (_in : F) (v : Z), True -> True -> ((v = 256%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma cutState_obligation1_trivial: forall (_in : F) (v : F), True -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma cutState_obligation2_trivial: forall (_in : F) (n2b : (list F)) (v : Z), True -> Forall (fun x35 => ((x35 = 0%F) \/ (x35 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 256%nat)) -> True -> ((v = 40%nat) -> True).
Proof. hammer. Qed.

Lemma cutState_obligation3: forall (_in : F) (n2b : (list F)) (d : (list F)) (v : Z), True -> Forall (fun x36 => ((x36 = 0%F) \/ (x36 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 256%nat)) -> Forall (fun x37 => ((x37 = 0%F) \/ (x37 = 1%F))) d -> ((d = (skipn 40%nat n2b)) /\ ((length d) = ((length n2b) - 40%nat)%nat)) -> True -> ((v = 216%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma cutState_obligation4: forall (_in : F) (n2b : (list F)) (d : (list F)) (v : (list F)), True -> Forall (fun x38 => ((x38 = 0%F) \/ (x38 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 256%nat)) -> Forall (fun x39 => ((x39 = 0%F) \/ (x39 = 1%F))) d -> ((d = (skipn 40%nat n2b)) /\ ((length d) = ((length n2b) - 40%nat)%nat)) -> Forall (fun x40 => ((x40 = 0%F) \/ (x40 = 1%F))) v -> True -> ((((v = (skipn 40%nat n2b)) /\ ((length v) = ((length n2b) - 40%nat)%nat)) /\ (v = d)) -> ((length v) = 216%nat)).
Proof. hammer. Qed.

Lemma cutState_obligation5: forall (_in : F) (n2b : (list F)) (d : (list F)) (v : F), True -> Forall (fun x41 => ((x41 = 0%F) \/ (x41 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 256%nat)) -> Forall (fun x42 => ((x42 = 0%F) \/ (x42 = 1%F))) d -> ((d = (skipn 40%nat n2b)) /\ ((length d) = ((length n2b) - 40%nat)%nat)) -> True -> (((v = 0%F) \/ (v = 1%F)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma cutState_obligation6: forall (_in : F) (n2b : (list F)) (d : (list F)) (v : F), True -> Forall (fun x24 => ((x24 = 0%F) \/ (x24 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 256%nat)) -> Forall (fun x25 => True) d -> ((d = (skipn 40%nat n2b)) /\ ((length d) = ((length n2b) - 40%nat)%nat)) -> True -> ((v = (as_le_f d)) -> (v = (as_le_f (drop 40%nat (to_le_f 256%nat _in))))).
Proof. 
  intuit. subst. f_equal. unfold drop. f_equal. rewrite <- H7.
  rewrite <- to_le_f_as_le_f;auto. 
Qed.
