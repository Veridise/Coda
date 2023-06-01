Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.
Require Import Coq.ZArith.Znat.


Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Arithmetic.PrimeFieldTheorems.

Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Ring.


From Circom Require Import Circom Default Util DSL Tuple ListUtil LibTactics Simplify.
From Circom Require Import Repr ReprZ.
From Circom.CircomLib Require Import Bitify Comparators Gates.

(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module CheckCarryToZero.

Module B := Bitify.
Module D := DSL.
Module Cmp := Comparators.
Module RZS := ReprZSigned.
Module RZ := RZS.RZ.

Import B.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Section _CheckCarryToZero.
Context {n m k: nat}.

Local Notation "[| xs |]" := (RZ.as_le n xs).

Definition cons (_in: F^k) :=
  let EPSILON := 1%nat in
  exists
  (carry: F^k)
  (carryRangeChecks: (@Num2Bits.t (m + EPSILON - n)) ^ k),
    D.iter (fun (i: nat) _cons => _cons /\
      (if (dec (i=0))%nat then
        _in[i] = carry[i] * 2^n
      else
        _in[i] + carry[i-1] = carry[i] * 2^n) /\
      carryRangeChecks[i].(Num2Bits._in) = carry[i] + 2^(m+EPSILON-n-1)
      )
      (k-1) True /\
    _in[k-1] + carry[k-2] = 0.

Local Close Scope F_scope.

Record t := {
  _in: F^k;
  _cons: cons _in
}.

End _CheckCarryToZero.
End CheckCarryToZero.