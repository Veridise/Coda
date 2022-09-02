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

Module Split.
Module B := Bitify.
Module D := DSL.
Module R := Repr.
Import R.

Import B.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Section _Split.
Context {n m: nat}.

(* // split a n + m bit input into two outputs
template Split(n, m) {
    assert(n <= 126);
    signal input in;
    signal output small;
    signal output big;

    small <-- in % (1 << n);
    big <-- in \ (1 << n);

    component n2b_small = Num2Bits(n);
    n2b_small.in <== small;
    component n2b_big = Num2Bits(m);
    n2b_big.in <== big;

    in === small + big * (1 << n);
} *)

Definition cons (_in: F) (small: F) (big: F) :=
  exists (n2b_small: @Num2Bits.t n) (n2b_big: @Num2Bits.t m),
  n2b_small.(Num2Bits._in) = small /\
  n2b_big.(Num2Bits._in) = big /\
  _in = small + big * 2^n.

Local Close Scope F_scope.

Record t := {
  _in: F;
  small: F;
  big: F;
  _cons: cons _in small big
}.

End _Split.
End Split.



Module SplitThree.
Module B := Bitify.
Module D := DSL.
Module R := Repr.
Import R.

Import B.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Section _SplitThree.
Context {n m k: nat}.

(* // split a n + m + k bit input into three outputs
template SplitThree(n, m, k) {
    assert(n <= 126);
    signal input in;
    signal output small;
    signal output medium;
    signal output big;

    small <-- in % (1 << n);
    medium <-- (in \ (1 << n)) % (1 << m);
    big <-- in \ (1 << n + m);

    component n2b_small = Num2Bits(n);
    n2b_small.in <== small;
    component n2b_medium = Num2Bits(m);
    n2b_medium.in <== medium;
    component n2b_big = Num2Bits(k);
    n2b_big.in <== big;

    in === small + medium * (1 << n) + big * (1 << n + m);
} *)

Definition cons (_in: F) (small: F) (medium: F) (big: F) :=
  exists (n2b_small: @Num2Bits.t n) (n2b_medium: @Num2Bits.t m) (n2b_big: @Num2Bits.t k),
  n2b_small.(Num2Bits._in) = small /\
  n2b_medium.(Num2Bits._in) = medium /\
  n2b_big.(Num2Bits._in) = big /\
  _in = small + medium * 2^n + big * 2^(n+m).

Local Close Scope F_scope.

Record t := {
  _in: F;
  small: F;
  medium: F;
  big: F;
  _cons: cons _in small medium big
}.

End _SplitThree.
End SplitThree.