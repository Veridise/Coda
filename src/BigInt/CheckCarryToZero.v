Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.

Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Arithmetic.PrimeFieldTheorems.

Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Ring.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.


Require Import Util DSL.
Require Import Circom.Circom Circom.Default.
Require Import Circom.LibTactics.
Require Import Circom.Tuple.
Require Import Circom.circomlib.Bitify Circom.circomlib.Comparators.
Require Import Circom.ListUtil.

(* Require Import VST.zlist.Zlist. *)


(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module CheckCarryToZero (C: CIRCOM).
Context {n: nat}.

Module B := Bitify C.
Module Cmp := Comparators C.
Module D := DSL C.
Import B C.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

(* x is a valid digit in base-2^n representation *)
Local Notation "x | ( n )" := (in_range n x) (at level 40).
Local Notation "xs |: ( n )" := (tforall (in_range n) xs) (at level 40).

(* interpret a tuple of weights as representing a little-endian base-2^n number *)
Local Notation "[| xs |]" := (as_le n xs).
Local Notation "' xs" := (to_list _ xs) (at level 20).

Section _CheckCarryToZero.
Context {n m k: nat}.

Definition cons (_in: F^k) :=
  let EPSILON := 1%nat in
  exists (carry: F^k) (carryRangeChecks: (Num2Bits.t (m + EPSILON - n)) ^ k),
    D.iter (fun (i: nat) _cons => _cons /\
      if (dec (i=0))%nat then
        _in[i] = carry[i] * 2^n
      else
        _in[i] + carry[i-1%nat] = carry[i] * 2^n)
      (k-1)%nat True /\
    _in[k-1] + carry[k-2] = 0.

Record t := {
  _in: F^k;
  _cons: cons _in
}.

Theorem soundness: forall (c: t), 
  [| 'c.(_in) |] = 0.
Proof.
Admitted.