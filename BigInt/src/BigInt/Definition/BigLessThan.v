Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.
Require Import Coq.Bool.Bool.

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

(* Require Import VST.zlist.Zlist. *)


(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module BigLessThan.

Module B := Bitify.
Module D := DSL.
Module Cmp := Comparators.
Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.
Module R := Repr.


Section _BigLessThan.
Context {n k: nat}.

Import Cmp Gates.


(* interpret a tuple of weights as representing a little-endian base-2^n number *)
Local Notation "[| xs |]" := (RZ.as_le n xs).
Notation "[\ xs \]" := (RZ.as_be n xs).

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Definition cons (a b: F^k) (out: F) : Prop :=
  exists (lt: (@LessThan.t n) ^ k) (eq: IsEqual.t ^ k),
  D.iter (fun i _cons => _cons /\
    lt[i].(LessThan._in)[0] = a[i] /\
    lt[i].(LessThan._in)[1] = b[i] /\
    eq[i].(IsEqual._in)[0] = a[i] /\
    eq[i].(IsEqual._in)[1] = b[i]) k True /\
  exists (ands: AND.t^k) (eq_ands: AND.t^k) (ors: OR.t^k),
  D.iter (fun j _cons => _cons /\
    let i := (k-2 - j)%nat in
    if ((i = k-2)%nat)? then
      ands[i].(AND.a) = eq[k-1].(IsEqual.out) /\
      ands[i].(AND.b) = lt[k-2].(LessThan.out) /\
      eq_ands[i].(AND.a) = eq[k-1].(IsEqual.out) /\
      eq_ands[i].(AND.b) = eq[k-2].(IsEqual.out) /\
      ors[i].(OR.a) = lt[k-1].(LessThan.out) /\
      ors[i].(OR.b) = ands[i].(AND.out)
    else
      ands[i].(AND.a) = eq_ands[i+1].(AND.out) /\
      ands[i].(AND.b) = lt[i].(LessThan.out) /\
      eq_ands[i].(AND.a) = eq_ands[i+1].(AND.out) /\
      eq_ands[i].(AND.b) = eq[i].(IsEqual.out) /\
      ors[i].(OR.a) = ors[i+1].(OR.out) /\
      ors[i].(OR.b) = ands[i].(AND.out))
    (k-1)%nat True /\
  out = ors[0].(OR.out).

Record t := {a: F^k; b: F^k; out: F; _cons: cons a b out}.

End _BigLessThan.
End BigLessThan.