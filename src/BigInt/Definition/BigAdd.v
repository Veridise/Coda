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

Module BigAdd.

Module B := Bitify.
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


Module ModSumThree.
Section ModSumThree.
Context {n: nat}.
Import B R.

(* Note: this is a simplified version from circom-pairing *)
(* 
template ModSumThree(n) {
  assert(n + 1 <= 253);
  signal input a;
  signal input b;
  signal input c;
  signal output sum;
  signal output carry;

  component n2b = Num2Bits(n + 1);
  n2b.in <== a + b + c;
  carry <== n2b.out[n];
  sum <== a + b + c - carry * (1 << n);
} 
*)

Definition cons (a b c sum carry: F) :=
  exists (n2b: @Num2Bits.t (S n)),
    n2b.(Num2Bits._in) = a + b + c /\
    carry = n2b.(Num2Bits.out) [n] /\
    sum = a + b + c - carry * 2^n.

Record t : Type := {
  a: F; b: F; c: F;
  sum: F; carry: F;
  _cons: cons a b c sum carry;
}.

(* for default values. never used *)
Definition wgen : t. skip. Defined.

#[global] Instance Default : Default (ModSumThree.t) := { default := wgen }.

End ModSumThree.
End ModSumThree.

Module M := ModSumThree.

Section _BigAdd.
Context {n k: nat}.

(* template BigAdd(n, k) {
    assert(n <= 252);
    signal input a[k];
    signal input b[k];
    signal output out[k + 1];

    component unit0 = ModSum(n);
    unit0.a <== a[0];
    unit0.b <== b[0];
    out[0] <== unit0.sum;

    component unit[k - 1];
    for (var i = 1; i < k; i++) {
        unit[i - 1] = ModSumThree(n);
        unit[i - 1].a <== a[i];
        unit[i - 1].b <== b[i];
        if (i == 1) {
            unit[i - 1].c <== unit0.carry;
        } else {
            unit[i - 1].c <== unit[i - 2].carry;
        }
        out[i] <== unit[i - 1].sum;
    }
    out[k] <== unit[k - 2].carry;
} *)

(* interpret a tuple of weights as representing a little-endian base-2^n number *)
Local Notation "[| xs |]" := (RZ.as_le n xs).
Local Notation "[|| xs ||]" := (RZ.as_le n ('xs)).

Definition cons (a b: tuple F k) (out: tuple F (S k)) :=
  exists (unit: tuple (@M.t n) k),
  D.iter (fun i _cons =>
    _cons /\
    unit [i].(M.a) = a [i] /\
    unit [i].(M.b) = b [i] /\
    (if (dec (i = 0)%nat) then
    unit [i].(M.c) = 0
    else
    unit [i].(M.c) = unit [i-1].(M.carry)) /\
    out [i] = unit [i].(M.sum)
    ) k True /\ 
  out [k] = unit [k-1].(M.carry).

Record t := {
  a: tuple F k;
  b: tuple F k;
  out: tuple F (S k);
  _cons: cons a b out
}.


End _BigAdd.
End BigAdd.
