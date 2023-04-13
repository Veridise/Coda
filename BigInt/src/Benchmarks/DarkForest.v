(** * DSL benchmark: Dark Forest *)

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

From Circom Require Import Circom DSL Util Default Tuple ListUtil LibTactics Signed Simplify Repr Coda.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Definition MiMCSponge (nInputs nRounds nOutputs : nat) (ins : list F) (KEY : F) : list F :=
  List.repeat 0%F nOutputs.

Local Notation "4" := (1 + 1 + 1 + 1)%F.
Local Notation "8" := (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)%F.

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

(** ** CalculateTotal *)

Lemma CalculateTotal_obligation0_trivial: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x0 => True) _in -> ((length _in) = n) -> True -> ((v = 0%nat) -> True).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation1_trivial: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x1 => True) _in -> ((length _in) = n) -> True -> (((0%nat <= v) /\ (v = n)) -> True).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation2_trivial: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x2 => True) _in -> ((length _in) = n) -> True -> (((0%nat <= v) /\ (v < n)) -> True).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation3_trivial: forall (n : nat) (_in : (list F)) (i : nat) (v : F), Forall (fun x3 => True) _in -> ((length _in) = n) -> (i < n) -> True -> ((v = (sum (take i _in))) -> True).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation4_trivial: forall (n : nat) (_in : (list F)) (i : nat) (x : F) (v : F), Forall (fun x4 => True) _in -> ((length _in) = n) -> (i < n) -> (x = (sum (take i _in))) -> True -> (((v = (sum (take i _in))) /\ (v = x)) -> True).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation5_trivial: forall (n : nat) (_in : (list F)) (i : nat) (x : F) (v : F), Forall (fun x5 => True) _in -> ((length _in) = n) -> (i < n) -> (x = (sum (take i _in))) -> True -> ((v = (_in!i)) -> True).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation6: forall (n : nat) (_in : (list F)) (i : nat) (x : F) (v : F), Forall (fun x6 => True) _in -> ((length _in) = n) -> (i < n) -> (x = (sum (take i _in))) -> True -> ((v = (x + (_in!i))%F) -> (v = (sum (take (i + 1%nat)%nat _in)))).
Proof.
  unfold take; intros; subst.
  apply sum_step; auto.
Qed.

Lemma CalculateTotal_obligation7: forall (n : nat) (_in : (list F)) (v : F), Forall (fun x7 => True) _in -> ((length _in) = n) -> True -> ((v = 0%F) -> (v = (sum (take 0%nat _in)))).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation8: forall (n : nat) (_in : (list F)) (v : F), Forall (fun x8 => True) _in -> ((length _in) = n) -> True -> ((v = (sum (take n _in))) -> (v = (sum _in))).
Proof.
  unfold take; intros; subst.
  rewrite firstn_all; auto.
Qed.

(** ** QuinSelector *)

(* TODO *)

(** IsNegative *)

Lemma IsNegative_obligation0: forall (_in : F) (v : Z), True -> True -> ((v = 254%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma IsNegative_obligation1_trivial: forall (_in : F) (v : F), True -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma IsNegative_obligation2: forall (_in : F) (z : (list F)) (v : (list F)), True -> Forall (fun x0 => ((x0 = 0%F) \/ (x0 = 1%F))) z -> (((as_le_f z) = _in) /\ ((length z) = 254%nat)) -> Forall (fun x1 => ((x1 = 0%F) \/ (x1 = 1%F))) v -> True -> (((((as_le_f v) = _in) /\ ((length v) = 254%nat)) /\ (v = z)) -> ((length v) = 254%nat)).
Proof. hammer. Qed.

Lemma IsNegative_obligation3: forall (_in : F) (z : (list F)) (v : F), True -> Forall (fun x2 => ((x2 = 0%F) \/ (x2 = 1%F))) z -> (((as_le_f z) = _in) /\ ((length z) = 254%nat)) -> True -> (((v = 0%F) \/ (v = 1%F)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma IsNegative_obligation4: forall (_in : F) (z : (list F)) (v : F), True -> Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) z -> (((as_le_f z) = _in) /\ ((length z) = 254%nat)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((Signed.to_Z (as_le_f z)) < 0%nat)) /\ ((v = 0%F) -> ~((Signed.to_Z (as_le_f z)) < 0%nat)))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((Signed.to_Z _in) < 0%nat)) /\ ((v = 0%F) -> ~((Signed.to_Z _in) < 0%nat))))).
Proof. hammer. Qed.

(** ** Random *)

Lemma Random_obligation0: forall (_in : (list F)) (KEY : F) (v : Z), Forall (fun x0 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> True -> ((v = 3%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma Random_obligation1: forall (_in : (list F)) (KEY : F) (v : Z), Forall (fun x1 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> True -> ((v = 4%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma Random_obligation2: forall (_in : (list F)) (KEY : F) (v : Z), Forall (fun x2 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> True -> ((v = 1%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma Random_obligation3: forall (_in : (list F)) (KEY : F) (v : (list F)), Forall (fun x3 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x4 => True) v -> True -> ((((forall (i:nat), 0%nat <= i < (length v) -> ((15%nat < C.q) /\ ((^ (v!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length v) = 3%nat)) /\ (v = _in)) -> ((length v) = 3%nat)).
Proof. hammer. Qed.

Lemma Random_obligation4_trivial: forall (_in : (list F)) (KEY : F) (v : F), Forall (fun x5 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> True -> ((((15%nat < C.q) /\ ((^ v) < (2%nat ^ 32%nat)%Z)) /\ (v = KEY)) -> True).
Proof. hammer. Qed.

Lemma Random_obligation5: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (v : Z), Forall (fun x6 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x7 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> True -> ((v = 254%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma Random_obligation6_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (v : F), Forall (fun x8 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x9 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> True -> (((v = (mimc!0%nat)) /\ (v = z)) -> True).
Proof. hammer. Qed.

Lemma Random_obligation7_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x10 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x11 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x12 => ((x12 = 0%F) \/ (x12 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = 8%F) -> True).
Proof. hammer. Qed.

Lemma Random_obligation8_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x13 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x14 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x15 => ((x15 = 0%F) \/ (x15 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = (n2b!3%nat)) -> True).
Proof. hammer. Qed.

Lemma Random_obligation9_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x16 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x17 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x18 => ((x18 = 0%F) \/ (x18 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = (8%F * (n2b!3%nat))%F) -> True).
Proof. hammer. Qed.

Lemma Random_obligation10_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x19 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x20 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x21 => ((x21 = 0%F) \/ (x21 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = 4%F) -> True).
Proof. hammer. Qed.

Lemma Random_obligation11_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x22 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x23 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x24 => ((x24 = 0%F) \/ (x24 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = (n2b!2%nat)) -> True).
Proof. hammer. Qed.

Lemma Random_obligation12_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x25 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x26 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x27 => ((x27 = 0%F) \/ (x27 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = (4%F * (n2b!2%nat))%F) -> True).
Proof. hammer. Qed.

Lemma Random_obligation13_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x28 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x29 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x30 => ((x30 = 0%F) \/ (x30 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = 2%F) -> True).
Proof. hammer. Qed.

Lemma Random_obligation14_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x31 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x32 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x33 => ((x33 = 0%F) \/ (x33 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = (n2b!1%nat)) -> True).
Proof. hammer. Qed.

Lemma Random_obligation15_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x34 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x35 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x36 => ((x36 = 0%F) \/ (x36 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = (2%F * (n2b!1%nat))%F) -> True).
Proof. hammer. Qed.

Lemma Random_obligation16_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x37 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x38 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x39 => ((x39 = 0%F) \/ (x39 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = (n2b!0%nat)) -> True).
Proof. hammer. Qed.

Lemma Random_obligation17_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x40 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x41 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x42 => ((x42 = 0%F) \/ (x42 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = ((2%F * (n2b!1%nat))%F + (n2b!0%nat))%F) -> True).
Proof. hammer. Qed.

Lemma Random_obligation18_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x43 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x44 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x45 => ((x45 = 0%F) \/ (x45 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = ((4%F * (n2b!2%nat))%F + ((2%F * (n2b!1%nat))%F + (n2b!0%nat))%F)%F) -> True).
Proof. hammer. Qed.

Lemma Random_obligation19: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x46 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x47 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x48 => ((x48 = 0%F) \/ (x48 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = ((8%F * (n2b!3%nat))%F + ((4%F * (n2b!2%nat))%F + ((2%F * (n2b!1%nat))%F + (n2b!0%nat))%F)%F)%F) -> ((^ v) <= 15%nat)).
Proof.
  unwrap_C; intros; subst; destruct H1, H6.
  assert (^n2b ! 0 <= 1). apply Repr.in_range_binary; auto.
  assert (^n2b ! 1 <= 1). apply Repr.in_range_binary; auto.
  assert (^n2b ! 2 <= 1). apply Repr.in_range_binary; auto.
  assert (^n2b ! 3 <= 1). apply Repr.in_range_binary; auto.
  repeat (autorewrite with F_to_Z; pose_nonneg; try (lia || nia)).
Qed.

(** ** RangeProof *)

Lemma RangeProof_obligation0_trivial: forall (bits : Z) (_in : F) (max_abs_value : F) (v : F), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation1_trivial: forall (bits : Z) (_in : F) (max_abs_value : F) (v : F), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> True -> ((v = 2%F) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation2: forall (bits : Z) (_in : F) (max_abs_value : F) (v : Z), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> True -> (((0%nat < v) /\ (v = bits)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma RangeProof_obligation3_trivial: forall (bits : Z) (_in : F) (max_abs_value : F) (v : F), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> True -> ((v = (2%F ^ (Z.to_N bits))%F) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation4_trivial: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (v : Z), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> True -> (((0%nat < v) /\ (v = bits)) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation5_trivial: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (v : Z), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> True -> ((v = 1%nat) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation6: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (v : Z), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> True -> ((v = (bits + 1%nat)%Z) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma RangeProof_obligation7_trivial: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (v : F), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> True -> (((v = (_in + (2%F ^ (Z.to_N bits))%F)%F) /\ (v = x)) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation8: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (n2b1 : (list F)) (v : Z), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> Forall (fun x0 => ((x0 = 0%F) \/ (x0 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ (Z.of_nat (length n2b1) = (bits + 1%nat)%Z)) -> True -> (((0%nat < v) /\ (v = bits)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma RangeProof_obligation9_trivial: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (n2b1 : (list F)) (v : F), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> Forall (fun x1 => ((x1 = 0%F) \/ (x1 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ (Z.of_nat (length n2b1) = (bits + 1%nat)%Z)) -> True -> (((0%nat <= (Signed.to_Z v)) /\ (v = max_abs_value)) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation10_trivial: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (v : Z), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^(Z.to_N bits))%F)%F) -> Forall (fun x2 => ((x2 = 0%F) \/ (x2 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ (Z.of_nat (length n2b1) = (bits + 1%nat)%Z)) -> Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ (Z.of_nat (length n2b2) = bits)) -> True -> (((0%nat < v) /\ (v = bits)) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation11_trivial: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (v : Z), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^(Z.to_N bits))%F)%F) -> Forall (fun x4 => ((x4 = 0%F) \/ (x4 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ (Z.of_nat (length n2b1) = (bits + 1%nat)%Z)) -> Forall (fun x5 => ((x5 = 0%F) \/ (x5 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ (Z.of_nat (length n2b2) = bits)) -> True -> ((v = 1%nat) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation12: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (v : Z), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> Forall (fun x6 => ((x6 = 0%F) \/ (x6 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ (Z.of_nat (length n2b1) = (bits + 1%nat)%Z)) -> Forall (fun x7 => ((x7 = 0%F) \/ (x7 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ (Z.of_nat (length n2b2) = bits)) -> True -> ((v = (bits + 1%nat)%Z) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof. Admitted.

Lemma RangeProof_obligation13_trivial: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (v : F), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> Forall (fun x8 => ((x8 = 0%F) \/ (x8 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ (Z.of_nat (length n2b1) = (bits + 1%nat)%Z)) -> Forall (fun x9 => ((x9 = 0%F) \/ (x9 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ (Z.of_nat (length n2b2) = bits)) -> True -> (((0%nat <= (Signed.to_Z v)) /\ (v = max_abs_value)) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation14_trivial: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (v : F), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> Forall (fun x10 => ((x10 = 0%F) \/ (x10 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ (Z.of_nat (length n2b1) = (bits + 1%nat)%Z)) -> Forall (fun x11 => ((x11 = 0%F) \/ (x11 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ (Z.of_nat (length n2b2) = bits)) -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation15: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (v : F), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> Forall (fun x12 => ((x12 = 0%F) \/ (x12 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ (Z.of_nat (length n2b1) = (bits + 1%nat)%Z)) -> Forall (fun x13 => ((x13 = 0%F) \/ (x13 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ (Z.of_nat (length n2b2) = bits)) -> True -> ((v = (max_abs_value + _in)%F) -> ((^ v) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)).
Proof. Admitted.

Lemma RangeProof_obligation16: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (v : F), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> Forall (fun x14 => ((x14 = 0%F) \/ (x14 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ (Z.of_nat (length n2b1) = (bits + 1%nat)%Z)) -> Forall (fun x15 => ((x15 = 0%F) \/ (x15 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ (Z.of_nat (length n2b2) = bits)) -> True -> ((v = 0%F) -> ((^ v) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)).
Proof. Admitted.

Lemma RangeProof_obligation17_trivial: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (v : Z), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> Forall (fun x16 => ((x16 = 0%F) \/ (x16 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ (Z.of_nat (length n2b1) = (bits + 1%nat)%Z)) -> Forall (fun x17 => ((x17 = 0%F) \/ (x17 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ (Z.of_nat (length n2b2) = bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> True -> (((0%nat < v) /\ (v = bits)) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation18_trivial: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (v : Z), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> Forall (fun x18 => ((x18 = 0%F) \/ (x18 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ (Z.of_nat (length n2b1) = (bits + 1%nat)%Z)) -> Forall (fun x19 => ((x19 = 0%F) \/ (x19 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ (Z.of_nat (length n2b2) = bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> True -> ((v = 1%nat) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation19: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (v : Z), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> Forall (fun x20 => ((x20 = 0%F) \/ (x20 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ (Z.of_nat (length n2b1) = (bits + 1%nat)%Z)) -> Forall (fun x21 => ((x21 = 0%F) \/ (x21 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ (Z.of_nat (length n2b2) = bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> True -> ((v = (bits + 1%nat)%Z) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof. Admitted.

Lemma RangeProof_obligation20_trivial: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (v : F), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> Forall (fun x22 => ((x22 = 0%F) \/ (x22 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ (Z.of_nat (length n2b1) = (bits + 1%nat)%Z)) -> Forall (fun x23 => ((x23 = 0%F) \/ (x23 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ (Z.of_nat (length n2b2) = bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> True -> ((v = 2%F) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation21_trivial: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (v : F), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> Forall (fun x24 => ((x24 = 0%F) \/ (x24 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ (Z.of_nat (length n2b1) = (bits + 1%nat)%Z)) -> Forall (fun x25 => ((x25 = 0%F) \/ (x25 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ (Z.of_nat (length n2b2) = bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> True -> (((0%nat <= (Signed.to_Z v)) /\ (v = max_abs_value)) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation22: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (v : F), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> Forall (fun x26 => ((x26 = 0%F) \/ (x26 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ (Z.of_nat (length n2b1) = (bits + 1%nat)%Z)) -> Forall (fun x27 => ((x27 = 0%F) \/ (x27 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ (Z.of_nat (length n2b2) = bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> True -> ((v = (2%F * max_abs_value)%F) -> ((^ v) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)).
Proof. Admitted.

Lemma RangeProof_obligation23_trivial: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (v : F), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> Forall (fun x28 => ((x28 = 0%F) \/ (x28 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ (Z.of_nat (length n2b1) = (bits + 1%nat)%Z)) -> Forall (fun x29 => ((x29 = 0%F) \/ (x29 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ (Z.of_nat (length n2b2) = bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> True -> (((0%nat <= (Signed.to_Z v)) /\ (v = max_abs_value)) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation24_trivial: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (v : F), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> Forall (fun x30 => ((x30 = 0%F) \/ (x30 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ (Z.of_nat (length n2b1) = (bits + 1%nat)%Z)) -> Forall (fun x31 => ((x31 = 0%F) \/ (x31 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ (Z.of_nat (length n2b2) = bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation25: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (v : F), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> Forall (fun x32 => ((x32 = 0%F) \/ (x32 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ (Z.of_nat (length n2b1) = (bits + 1%nat)%Z)) -> Forall (fun x33 => ((x33 = 0%F) \/ (x33 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ (Z.of_nat (length n2b2) = bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> True -> ((v = (max_abs_value + _in)%F) -> ((^ v) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)).
Proof. Admitted.

Lemma RangeProof_obligation26_trivial: forall (bits : Z) (_in : F) (max_abs_value : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (lt2 : F) (v : unit), (0%nat < bits) -> True -> (0%nat <= (Signed.to_Z max_abs_value)) -> (x = (_in + (2%F ^ (Z.to_N bits))%F)%F) -> Forall (fun x34 => ((x34 = 0%F) \/ (x34 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ (Z.of_nat (length n2b1) = (bits + 1%nat)%Z)) -> Forall (fun x35 => ((x35 = 0%F) \/ (x35 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ (Z.of_nat (length n2b2) = bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> (((lt2 = 0%F) \/ (lt2 = 1%F)) /\ (((lt2 = 1%F) -> ((^ (2%F * max_abs_value)%F) < (^ (max_abs_value + _in)%F))) /\ ((lt2 = 0%F) -> ~((^ (2%F * max_abs_value)%F) < (^ (max_abs_value + _in)%F))))) -> True -> ((lt2 = 0%F) -> True).
Proof. hammer. Qed.
