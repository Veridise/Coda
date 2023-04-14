(** * DSL benchmark: ModSumThree, BigAdd, BigAddModP *)

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

From Circom Require Import Circom Util Default Tuple ListUtil LibTactics Simplify Repr ReprZ Coda Signed.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.


Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.
Definition as_le := RZ.as_le.
Local Notation "[| xs | n ]" := (RZ.as_le n xs).
Local Notation "[| xs |]" := (Repr.as_le 1%nat xs).


#[local]Hint Extern 1 (Forall _ (firstn _ _)) => apply Forall_firstn: core.
#[local]Hint Extern 1  => match goal with
   | [ |- context[List_nth_Default _ _] ] => unfold_default end: core.
   #[local]Hint Extern 1  => match goal with
   | [ |- context[List.nth  _ _ _] ] => apply Forall_nth end: core.
#[local]Hint Extern 1 => match goal with
  [ |- context[length _] ] => rewrite_length end: core.
#[local]Hint Extern 1 (Forall _ (skipn _ _)) => apply Forall_skipn: core.

#[local]Hint Extern 1 (Forall _ (_ :: _)) => constructor: core.
#[local]Hint Extern 1 (Z.of_N (N.of_nat _)) => rewrite nat_N_Z: core.
#[local]Hint Extern 1  => repeat match goal with
  [ H: context[Z.of_N (N.of_nat _)] |- _] => rewrite nat_N_Z in H end: core.

#[local]Hint Extern 1 (_ < _) => lia: core.
#[local]Hint Extern 1 (_ < _)%nat => lia: core.
#[local]Hint Extern 1 (_ <= _) => lia: core.
#[local]Hint Extern 1 (_ <= _)%nat => lia: core.
#[local]Hint Extern 1 (_ > _) => lia: core.
#[local]Hint Extern 1 (_ > _)%nat => lia: core.
#[local]Hint Extern 1 (_ >= _) => lia: core.
#[local]Hint Extern 1 (_ >= _)%nat => lia: core.
#[local]Hint Extern 1 (S _ = S _) => f_equal: core.
#[local]Hint Extern 1 (@eq (F.F q) _ _) => fqsatz: core. 

Lemma Switcher_obligation0_trivial: forall (sel : F) (L : F) (R : F) (v : F), ((sel = 0%F) \/ (sel = 1%F)) -> True -> True -> True -> ((v = R) -> True).
Proof. hammer. Qed.

Lemma Switcher_obligation1_trivial: forall (sel : F) (L : F) (R : F) (v : F), ((sel = 0%F) \/ (sel = 1%F)) -> True -> True -> True -> ((v = L) -> True).
Proof. hammer. Qed.

Lemma Switcher_obligation2_trivial: forall (sel : F) (L : F) (R : F) (v : F), ((sel = 0%F) \/ (sel = 1%F)) -> True -> True -> True -> ((v = (R - L)%F) -> True).
Proof. hammer. Qed.

Lemma Switcher_obligation3_trivial: forall (sel : F) (L : F) (R : F) (v : F), ((sel = 0%F) \/ (sel = 1%F)) -> True -> True -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (v = sel)) -> True).
Proof. hammer. Qed.

Lemma Switcher_obligation4_trivial: forall (sel : F) (L : F) (R : F) (aux : F) (v : F), ((sel = 0%F) \/ (sel = 1%F)) -> True -> True -> (aux = ((R - L)%F * sel)%F) -> True -> (((v = ((R - L)%F * sel)%F) /\ (v = aux)) -> True).
Proof. hammer. Qed.

Lemma Switcher_obligation5_trivial: forall (sel : F) (L : F) (R : F) (aux : F) (v : F), ((sel = 0%F) \/ (sel = 1%F)) -> True -> True -> (aux = ((R - L)%F * sel)%F) -> True -> ((v = L) -> True).
Proof. hammer. Qed.

Lemma Switcher_obligation6: forall (sel : F) (L : F) (R : F) (aux : F) (v : F), ((sel = 0%F) \/ (sel = 1%F)) -> True -> True -> (aux = ((R - L)%F * sel)%F) -> True -> ((v = (aux + L)%F) -> (((sel = 0%F) -> (v = L)) /\ (~((sel = 0%F)) -> (v = R)))).
Proof. 
  unwrap_C. intuit; subst; try (fqsatz || (exfalso; fqsatz)).
Qed.

Lemma Switcher_obligation7_trivial: forall (sel : F) (L : F) (R : F) (aux : F) (v : F), ((sel = 0%F) \/ (sel = 1%F)) -> True -> True -> (aux = ((R - L)%F * sel)%F) -> True -> ((v = 0%F) -> True).
Proof. hammer. Qed.

Lemma Switcher_obligation8_trivial: forall (sel : F) (L : F) (R : F) (aux : F) (v : F), ((sel = 0%F) \/ (sel = 1%F)) -> True -> True -> (aux = ((R - L)%F * sel)%F) -> True -> (((v = ((R - L)%F * sel)%F) /\ (v = aux)) -> True).
Proof. hammer. Qed.

Lemma Switcher_obligation9_trivial: forall (sel : F) (L : F) (R : F) (aux : F) (v : F), ((sel = 0%F) \/ (sel = 1%F)) -> True -> True -> (aux = ((R - L)%F * sel)%F) -> True -> ((v = (0%F - aux)%F) -> True).
Proof. hammer. Qed.

Lemma Switcher_obligation10_trivial: forall (sel : F) (L : F) (R : F) (aux : F) (v : F), ((sel = 0%F) \/ (sel = 1%F)) -> True -> True -> (aux = ((R - L)%F * sel)%F) -> True -> ((v = R) -> True).
Proof. hammer. Qed.

Lemma Switcher_obligation11: forall (sel : F) (L : F) (R : F) (aux : F) (v : F), ((sel = 0%F) \/ (sel = 1%F)) -> True -> True -> (aux = ((R - L)%F * sel)%F) -> True -> ((v = ((0%F - aux)%F + R)%F) -> (((sel = 0%F) -> (v = R)) /\ (~((sel = 0%F)) -> (v = L)))).
Proof. 
  unwrap_C. intuit; subst; try (fqsatz || (exfalso; fqsatz)).
Qed.

Lemma Switcher_obligation12_trivial: forall (sel : F) (L : F) (R : F) (aux : F), ((sel = 0%F) \/ (sel = 1%F)) -> True -> True -> (aux = ((R - L)%F * sel)%F) -> (True -> True).
Proof. hammer. Qed.