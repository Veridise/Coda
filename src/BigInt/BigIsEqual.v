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

Module BigIsEqual.
Context {n: nat}.

Module C := Comparators.
Module D := DSL.
Module R := Repr.
Import R.
Import C.
Import B.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Section _BigIsEqual.
Context {k: nat}.

(* // check if k-register variables a, b are equal everywhere
template BigIsEqual(k) {
    signal input a[k];
    signal input b[k];
    signal output out;

    component isEquals[k];
    var total = k;
    for (var i = 0; i < k; i ++) {
        isEquals[i] = IsEqual();
        isEquals[i].in[0] <== a[i];
        isEquals[i].in[1] <== b[i];
        total -= isEquals[i].out;
    }
    component checkZero = IsZero();
    checkZero.in <== total;
    out <== checkZero.out;
} *)

Definition cons (a: F^k) (b: F^k) (out: F) :=
  exists (isEquals: IsEqual.t ^ k) (checkZero: @IsZero.t),
  let total := F.of_nat q k in 
  let '(total, _C) := 
    (D.iter (fun i '(total, _cons) =>
      (total - isEquals[i].(IsEqual.out),
      _cons /\
      isEquals[i].(IsEqual._in)[0] = a[i] /\
      isEquals[i].(IsEqual._in)[1] = b[i]
      )) k (total, True)) in
  checkZero.(IsZero._in) = total /\
  out = checkZero.(IsZero.out) /\
  _C.

Local Close Scope F_scope.

Record t := {
  a: F^k;
  b: F^k;
  out: F;
  _cons: cons a b out
}.

Local Open Scope F_scope. 

Theorem soundness: forall (c: t), 
  if (forallb (fun x => (fst x = snd x)? ) (ListUtil.map2 pair (' c.(a)) (' c.(b)))) then
  c.(out) = 1
  else
  c.(out) = 0.
Proof.
  unwrap_C. intros c. 
  destruct c as [a b out _cons]. 
  destruct _cons as [isEquals [checkZero]]. subst. simpl in *.
Admitted.

End _BigIsEqual.
End BigIsEqual.
