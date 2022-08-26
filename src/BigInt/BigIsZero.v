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

From Circom Require Import Circom Default Util DSL Tuple ListUtil LibTactics Simplify.
From Circom Require Import Repr ReprZ.
From Circom.CircomLib Require Import Bitify Comparators Gates.

(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module BigIsZero.

Module D := DSL.
Module R := Repr.
Module C := Comparators.
Import R.
Import C.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Section _BigIsZero.
Context {k: nat}.

(* // check if k-register variable a is equal to zero
template BigIsZero(k) {
    signal input in[k];
    signal output out;

    component isZeros[k];
    var total = k;
    for (var i = 0; i < k; i ++) {
        isZeros[i] = IsZero();
        isZeros[i].in <== in[i];
        total -= isZeros[i].out;
    }
    component checkZero = IsZero();
    checkZero.in <== total;
    out <== checkZero.out;
} *)

Definition cons (_in: F^k) (out: F) :=
  exists (isZeros: @IsZero.t ^ k) (checkZero: @IsZero.t),
  let total := F.of_nat q k in 
  let '(total, _C) := 
    (D.iter (fun i '(total, _cons) =>
      (total - isZeros[i].(IsZero.out),
      _cons /\
      isZeros[i].(IsZero._in) = _in[i]
      )) k (total, True)) in
  checkZero.(IsZero._in) = total /\
  out = checkZero.(IsZero.out) /\
  _C.

Local Close Scope F_scope.

Record t := {
  _in: F^k;
  out: F;
  _cons: cons _in out
}.

Local Open Scope F_scope. 

Theorem soundness: forall (c: t), 
  if (forallb (fun x => (x = 0)? ) (' c.(_in))) then
  c.(out) = 1
  else
  c.(out) = 0.
Proof.
  unwrap_C. intros c. 
  destruct c as [_in out _cons]. 
  destruct _cons as [isZeros [checkZero]]. subst. simpl in *.
Admitted.

End _BigIsZero.
End BigIsZero.
