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

Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Decidable Crypto.Util.Notations.
Require Import BabyJubjub.
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Ring.

Require Import Util DSL.
Require Import Circom.circomlib.Bitify.

(* Require Import VST.zlist.Zlist. *)

Require Import Circom.Circom.
Require Import Circom.ECC.Polynom.

(* Circuit:
* https://github.com/0xPARC/circom-ecdsa/blob/08c2c905b918b563c81a71086e493cb9d39c5a08/circuits/bigint.circom
*)

Module BigInt (C: CIRCOM).

Module B := Bitify C.
Import B C.

Local Open Scope list_scope.
Local Open Scope F_scope.

Local Notation "x [ i ]" := (nth_default 0 i x).
Local Notation "2" := (1 + 1 : F).

Coercion N.of_nat: nat >-> N.
 
Definition ModSum_cons (n: nat) (a b sum carry: F) :=
  exists (n2b: Num2Bits.t),
    n2b.(Num2Bits._in) = a+b /\
    n2b.(Num2Bits._out)[n] = carry /\
    sum = a + b - carry * 2^n.

(* TODO: define mod and quotient in F *)
Definition ModSum_spec (n: nat) (a b sum carry: F) :=
  sum + carry * 2^n = a + b.

Lemma ModSum_sound (n: nat) (a b sum carry: F):
  ModSum_cons n a b sum carry ->
  ModSum_spec n a b sum carry.
Proof.
  unwrap_C.
  unfold ModSum_cons, ModSum_spec.
  intros H. destruct H as [n2b H]. intuition idtac.
  pose proof Num2Bits.soundness as Hn2b. specialize (Hn2b n2b). unfold Num2Bits.spec, Num2Bits.repr_binary in Hn2b.
  intuition idtac.
  fqsatz.
Qed.