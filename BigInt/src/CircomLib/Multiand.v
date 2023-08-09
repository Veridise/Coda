(* Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.Znumtheory.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Coq.Bool.Bool.


Require Import Circom.Tuple.
Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import BabyJubjub.
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Crypto.Algebra.Ring Crypto.Algebra.Field.

From Circom Require Import Circom Default LibTactics Util.
Require Import Circom.Circom Circom.Default.

(* Circuit:
* https://github.com/iden3/circomlib/blob/master/circuits/gates.circom
*)

Local Open Scope list_scope.
Local Open Scope F_scope. *)

(** * DSL benchmark: Gates *)

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

From Circom Require Import Circom Util Default Tuple LibTactics Simplify ListUtil Repr Coda.
From Circom.CircomLib Require Import Bitify.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

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
#[local]Hint Extern 1 False => fqsatz: core. 

(* * Automatically generated *)

Module MultiAND.

#[local] Hint Extern 10 (_ = _) => fqsatz : core.
#[local] Hint Extern 10 (binary _) => (left; fqsatz) || (right; fqsatz): core.

Lemma MultiAND_obligation0_trivial: forall (in_0 : F) (in_1 : F) (var_0 : F) (and1_a : F) (and1_b : F) (v : F), True -> True -> (var_0 = 1%F) -> (and1_a = in_0) -> (and1_b = in_1) -> True -> (((v = in_0) /\ (v = and1_a)) -> True).
Proof. hammer. Qed.

Lemma MultiAND_obligation1_trivial: forall (in_0 : F) (in_1 : F) (var_0 : F) (and1_a : F) (and1_b : F) (v : F), True -> True -> (var_0 = 2%F) -> (and1_a = in_0) -> (and1_b = in_1) -> True -> (((v = in_1) /\ (v = and1_b)) -> True).
Proof. hammer. Qed.

Lemma MultiAND_obligation2_trivial: forall (in_0 : F) (in_1 : F) (var_0 : F) (and1_a : F) (and1_b : F) (and1_out : F) (out : F) (v : F), True -> True -> (var_0 = 2%F) -> (and1_a = in_0) -> (and1_b = in_1) -> (and1_out = (and1_a * and1_b)%F) -> ((out = (and1_a * and1_b)%F) /\ (out = and1_out)) -> True -> ((((v = (and1_a * and1_b)%F) /\ (v = and1_out)) /\ (v = out)) -> True).
Proof. hammer. Qed.

End MultiAND.