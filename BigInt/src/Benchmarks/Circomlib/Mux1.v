(** * DSL benchmark: MultiMux1 *)

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

From Circom Require Import Circom Util Default Tuple ListUtil LibTactics Simplify Repr Coda.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Lemma MultiMux1_obligation0_trivial: forall (n : nat) (c : (list (list F))) (s : F) (x : (list F)) (a : F) (b : F) (v : F), Forall (fun x1 => Forall (fun x0 => True) x1) c -> Forall (fun x1 => ((length x1) = 2%nat)) c -> ((length c) = n) -> True -> Forall (fun x2 => True) x -> ((length x) = 2%nat) -> (a = (x!0%nat)) -> (b = (x!1%nat)) -> True -> (((v = b) /\ True) -> True).
Proof. hammer. Qed.

Lemma MultiMux1_obligation1_trivial: forall (n : nat) (c : (list (list F))) (s : F) (x : (list F)) (a : F) (b : F) (v : F), Forall (fun x4 => Forall (fun x3 => True) x4) c -> Forall (fun x4 => ((length x4) = 2%nat)) c -> ((length c) = n) -> True -> Forall (fun x5 => True) x -> ((length x) = 2%nat) -> (a = (x!0%nat)) -> (b = (x!1%nat)) -> True -> (((v = a) /\ True) -> True).
Proof. hammer. Qed.

Lemma MultiMux1_obligation2_trivial: forall (n : nat) (c : (list (list F))) (s : F) (x : (list F)) (a : F) (b : F) (y : F) (v : F), Forall (fun x7 => Forall (fun x6 => True) x7) c -> Forall (fun x7 => ((length x7) = 2%nat)) c -> ((length c) = n) -> True -> Forall (fun x8 => True) x -> ((length x) = 2%nat) -> (a = (x!0%nat)) -> (b = (x!1%nat)) -> (y = (b - a)%F) -> True -> (((v = y) /\ True) -> True).
Proof. hammer. Qed.

Lemma MultiMux1_obligation3_trivial: forall (n : nat) (c : (list (list F))) (s : F) (x : (list F)) (a : F) (b : F) (y : F) (v : F), Forall (fun x10 => Forall (fun x9 => True) x10) c -> Forall (fun x10 => ((length x10) = 2%nat)) c -> ((length c) = n) -> True -> Forall (fun x11 => True) x -> ((length x) = 2%nat) -> (a = (x!0%nat)) -> (b = (x!1%nat)) -> (y = (b - a)%F) -> True -> (((v = s) /\ True) -> True).
Proof. hammer. Qed.

Lemma MultiMux1_obligation4_trivial: forall (n : nat) (c : (list (list F))) (s : F) (x : (list F)) (a : F) (b : F) (y : F) (z : F) (v : F), Forall (fun x13 => Forall (fun x12 => True) x13) c -> Forall (fun x13 => ((length x13) = 2%nat)) c -> ((length c) = n) -> True -> Forall (fun x14 => True) x -> ((length x) = 2%nat) -> (a = (x!0%nat)) -> (b = (x!1%nat)) -> (y = (b - a)%F) -> (z = (y * s)%F) -> True -> (((v = z) /\ True) -> True).
Proof. hammer. Qed.

Lemma MultiMux1_obligation5_trivial: forall (n : nat) (c : (list (list F))) (s : F) (x : (list F)) (a : F) (b : F) (y : F) (z : F) (v : F), Forall (fun x16 => Forall (fun x15 => True) x16) c -> Forall (fun x16 => ((length x16) = 2%nat)) c -> ((length c) = n) -> True -> Forall (fun x17 => True) x -> ((length x) = 2%nat) -> (a = (x!0%nat)) -> (b = (x!1%nat)) -> (y = (b - a)%F) -> (z = (y * s)%F) -> True -> (((v = a) /\ True) -> True).
Proof. hammer. Qed.

Lemma MultiMux1_obligation6_trivial: forall (n : nat) (c : (list (list F))) (s : F) (x : (list F)) (a : F) (b : F) (y : F) (z : F) (v : F), Forall (fun x19 => Forall (fun x18 => True) x19) c -> Forall (fun x19 => ((length x19) = 2%nat)) c -> ((length c) = n) -> True -> Forall (fun x20 => True) x -> ((length x) = 2%nat) -> (a = (x!0%nat)) -> (b = (x!1%nat)) -> (y = (b - a)%F) -> (z = (y * s)%F) -> True -> ((v = (z + a)%F) -> True).
Proof. hammer. Qed.

Lemma MultiMux1_obligation7: forall (n : nat) (c : (list (list F))) (s : F) (v : (list F)), Forall (fun x22 => Forall (fun x21 => True) x22) c -> Forall (fun x22 => ((length x22) = 2%nat)) c -> ((length c) = n) -> True -> Forall (fun x23 => True) v -> True -> (True -> ((length v) = 2%nat)).
Proof. Admitted.

Lemma MultiMux1_obligation8: forall (n : nat) (c : (list (list F))) (s : F) (v : (list F)), Forall (fun x25 => Forall (fun x24 => True) x25) c -> Forall (fun x25 => ((length x25) = 2%nat)) c -> ((length c) = n) -> True -> Forall (fun x26 => True) v -> True -> (((forall (im:nat), 0%nat <= im < (length c) -> True) /\ ((length v) = (length c))) -> ((forall (i:nat), 0%nat <= i < n -> ((v!i) = (((((c!i)!1%nat) - ((c!i)!0%nat))%F * s)%F + ((c!i)!0%nat))%F)) /\ ((length v) = n))).
Proof. Admitted.
