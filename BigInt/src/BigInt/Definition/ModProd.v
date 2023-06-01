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

From Circom Require Import Circom Default Util DSL Tuple ListUtil LibTactics Simplify.
From Circom Require Import Repr ReprZ.
From Circom.CircomLib Require Import Bitify Comparators.

(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module ModProd.

Module D := DSL.
Module Cmp := Comparators.
Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.
Module R := Repr.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Module N := Bitify.Num2Bits.
Module B := Bitify.Bits2Num.

Section _ModProd.
Context {n: nat}.

Definition cons (a b prod carry: F) := 
  exists n2b: (@N.t (2*n)),
  n2b.(N._in) = a*b /\
  exists (b2n1: @B.t n) (b2n2: @B.t n),
  D.iter (fun (i: nat) (cons : Prop) => cons /\
    b2n1.(B._in)[i] = n2b.(N.out)[i] /\
    b2n2.(B._in)[i] = n2b.(N.out)[i + n])
  n True /\
  prod = b2n1.(B.out) /\
  carry = b2n2.(B.out).

Record t := { a: F; b: F; prod: F; carry: F; _cons: cons a b prod carry}.

End _ModProd.
End ModProd.