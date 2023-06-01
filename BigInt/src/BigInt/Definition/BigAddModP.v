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

Module BigAddModP.

Module B := Bitify.
Module D := DSL.
Module Cmp := Comparators.
Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.
Module R := Repr.
Module Add := BigAdd.
Module Sub := BigSub.
Module Lt := BigLessThan.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Section _BigAddModP.
Context {n k: nat}.


Definition cons (a b p out: F^k) :=
  exists (add: @Add.t n k) (lt: @Lt.t n (S k)) (sub: @Sub.t n (S k)),
  D.iter (fun i _cons => _cons /\
    add.(Add.a)[i] = a[i] /\
    add.(Add.b)[i] = b[i]) k True /\
  D.iter (fun i _cons => _cons /\
    lt.(Lt.a)[i] = add.(Add.out)[i] /\
    lt.(Lt.b)[i] = p[i]) k True /\
  lt.(Lt.a)[k] = add.(Add.out)[k] /\
  lt.(Lt.b)[k] = 0 /\
  D.iter (fun i _cons => _cons /\
    sub.(Sub.a)[i] = add.(Add.out)[i] /\
    sub.(Sub.b)[i] = (1 - lt.(Lt.out)) * p[i]) k True /\
  sub.(Sub.a)[k] = add.(Add.out)[k] /\
  sub.(Sub.b)[k] = 0 /\
  sub.(Sub.out)[k] = 0 /\
  D.iter (fun i _cons => _cons /\
    out[i] = sub.(Sub.out)[i]) k True.
  
Record t := { a: F^k; b: F^k; p: F^k; out: F^k; _cons: cons a b p out }.

End _BigAddModP.
End BigAddModP.