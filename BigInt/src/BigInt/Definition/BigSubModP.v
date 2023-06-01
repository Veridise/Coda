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
From Circom.BigInt.Definition Require Import BigAdd BigLessThan BigSub.

(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module BigSubModP.

Module B := Bitify.
Module D := DSL.
Module Cmp := Comparators.
Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.
Module R := Repr.
Module Add := BigAdd.
Module Sub := BigSub.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Section _BigSubModP.
Context {n k: nat}.


Definition cons (a b p out: F^k) :=
  exists (sub: @Sub.t n k) (add: @Add.t n k) (tmp: F^n),
  D.iter (fun (i: nat) (_cons: Prop) => _cons /\
    sub.(Sub.a)[i] = a[i] /\
    sub.(Sub.b)[i] = b[i]) k True /\
  let flag := sub.(Sub.underflow) in
  D.iter (fun (i: nat) (_cons: Prop) => _cons /\
    add.(Add.a)[i] = sub.(Sub.out)[i] /\
    add.(Add.b)[i] = p[i]) k True /\
  D.iter (fun (i: nat) (_cons: Prop) => _cons /\
    tmp[i] = (1 - flag) * sub.(Sub.out)[i] /\
    out[i] = tmp[i] + flag * add.(Add.out)[i]) k True.

Record t := { a: F^k; b: F^k; p: F^k; out: F^k; _cons: cons a b p out }.

End _BigSubModP.
End BigSubModP.