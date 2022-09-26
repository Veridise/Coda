(* This file is part of the Coda project, which contains the specification of 
   the BigInt library.  *)
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

From Circom.BigInt.Definition Require Import 
      BigIsZero BigIsEqual ModProd BigAdd BigSub BigLessThan BigAddModP
      BigSubModP CheckCarryToZero Split BigMult BigMod.

From Circom.BigInt.Proof Require Import 
      BigIsZero BigIsEqual ModProd BigAdd BigSub BigLessThan BigAddModP
      BigSubModP CheckCarryToZero Split BigMult BigMod.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.
Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Local Notation "[| xs |] '_' n" := (ReprZUnsigned.RZ.as_le n xs) (at level 2).
Local Notation "a ?=? b" := ((a?) = (b?)) (at level 70).

(* BigIsZero *)
Theorem BigIsZero_Soundness {k: nat}: forall (c: @BigIsZero.t k),
  1 <= k <= C.k ->
  if (forallb (fun x => (x = 0)? ) (' c.(BigIsZero._in))) then
  c.(BigIsZero.out) = 1
  else
  c.(BigIsZero.out) = 0.
Proof.
  exact BigIsZero.soundness.
Qed.

(* BigIsEqual *)
Theorem BigIsEqual_Soundness {k: nat}: forall (c: @BigIsEqual.t k), 
  1 <= k <= C.k ->
  if (forallb (fun x => (fst x = snd x)? ) 
      (ListUtil.map2 pair (' c.(BigIsEqual.a)) (' c.(BigIsEqual.b)))) then
  c.(BigIsEqual.out) = 1
  else
  c.(BigIsEqual.out) = 0.
Proof.
  exact BigIsEqual.soundness.
Qed.

(* ModProd *)
Theorem ModProd_Soundness {n: nat}: forall (c: @ModProd.t n),
  2 * n <= k ->
  let '(a,b,prod,carry) := (c.(ModProd.a), c.(ModProd.b), c.(ModProd.prod), c.(ModProd.carry)) in
  carry * 2^n + prod = a * b /\
  prod | (n).
Proof.
  exact ModProd.soundness.
Qed.

(* ModSumThree *)
Module ModSumThree := BigAdd.ModSumThree.
Theorem ModSumThree_Soundness {n: nat}: forall (w: @ModSumThree.t n),
  (* pre-conditions *)
  ( n <= C.k - 1 )%Z ->
  (* a and b are n-bits, i.e., <= 2^n-1 *)
  w.(ModSumThree.a) | (n) -> 
  w.(ModSumThree.b) | (n) -> 
  binary w.(ModSumThree.c) ->
  (* post-conditions *)
  w.(ModSumThree.sum) + 2^n * w.(ModSumThree.carry) = 
  w.(ModSumThree.a) + w.(ModSumThree.b) + w.(ModSumThree.c) /\
  (* sum is n-bits, i.e., <= 2^n-1 *)
  w.(ModSumThree.sum) | (n) /\
  binary w.(ModSumThree.carry).
Proof.
  exact ModSumThree.soundness.
Qed.

(* BigAdd *)
Theorem BigAdd_Soundness {n k: nat}: forall (w: @BigAdd.t n k),
  (* pre-condition *)
  n > 0 ->
  k > 0 ->
  (n + 1 <= C.k)%Z ->
  (* a and b are proper big int *)
  'w.(BigAdd.a) |: (n) ->
  'w.(BigAdd.b) |: (n) ->
  (* post-condition *)
  ([|' w.(BigAdd.out) |] _ n = [|' w.(BigAdd.a) |] _ n + [|' w.(BigAdd.b) |] _ n)%Z /\
  'w.(BigAdd.out) |: (n).
Proof.
  exact BigAdd.soundness.
Qed.

(* ModSubThree *)
Module ModSubThree := BigSub.ModSubThree.
Theorem ModSubThree_Soundness {n: nat}: forall (w: @ModSubThree.t n),
  (* pre-conditions *)
  n + 2 <= C.k ->
  (* a and b are n-bits, i.e., <= 2^n-1 *)
  w.(ModSubThree.a) | (n) -> 
  w.(ModSubThree.b) | (n) -> 
  binary w.(ModSubThree.c) ->
  (* post-conditions *)
  w.(ModSubThree.out) = 
    (w.(ModSubThree.a) + w.(ModSubThree.borrow) * 2^n) 
    - w.(ModSubThree.b) - w.(ModSubThree.c) /\
  w.(ModSubThree.out) | (n) /\
  binary w.(ModSubThree.borrow) /\
  w.(ModSubThree.borrow) = 1 ?=? w.(ModSubThree.a) <q (w.(ModSubThree.b)+w.(ModSubThree.c)).
Proof.
  exact ModSubThree.soundness.
Qed.

(* BigSub *)
Theorem BigSub_Soundness {n k: nat}: forall (w: @BigSub.t n k),
  (* pre-condition *)
  0 < n ->
  0 < k ->
  n + 2 <= C.k ->
  'w.(BigSub.a) |: (n) ->
  'w.(BigSub.b) |: (n) ->
  (* post-condition *)
  ([|' w.(BigSub.out) |] _ n = [|' w.(BigSub.a) |] _ n - [|' w.(BigSub.b) |] _ n + ^ w.(BigSub.underflow)  * 2^(n*k))%Z /\
  'w.(BigSub.out) |: (n) /\
  binary w.(BigSub.underflow) /\
  (w.(BigSub.underflow) = 1 ?=? ([|' w.(BigSub.a) |] _ n < [|' w.(BigSub.b) |] _ n)).
Proof.
  exact BigSub.soundness.
Qed.

Theorem BigSub_Soundness_ite {n k: nat}: forall (w: @BigSub.t n k),
  (* pre-conditions *)
  0 < n ->
  0 < k ->
  n + 2 <= C.k ->
  'w.(BigSub.a) |: (n) ->
  'w.(BigSub.b) |: (n) ->
  (* post-conditions *)
  binary w.(BigSub.underflow) /\
  'w.(BigSub.out) |: (n) /\
  if dec ([|'w.(BigSub.a)|] _ n >= [|'w.(BigSub.b)|] _ n) then
    w.(BigSub.underflow) = 0 /\
    ([|' w.(BigSub.out) |] _ n = [|' w.(BigSub.a) |] _ n - [|' w.(BigSub.b) |] _ n)%Z
  else
    w.(BigSub.underflow) = 1 /\
    ([|' w.(BigSub.out) |] _ n = 2^(n*k) * ^w.(BigSub.underflow)  + [|' w.(BigSub.a) |] _ n - [|' w.(BigSub.b) |] _ n)%Z
  .
Proof.
  exact BigSub.soundness_ite.
Qed.

(* BigLessThan *)
Theorem BigLessThan_Soundness {n k: nat}: forall (c: @BigLessThan.t n k),
  n <= C.k - 1 ->
  2 <= k ->
  'c.(BigLessThan.a) |: (n) ->
  'c.(BigLessThan.b) |: (n) ->
  binary c.(BigLessThan.out) /\
  (c.(BigLessThan.out) = 1%F <-> [|' c.(BigLessThan.a) |] _ n < [|' c.(BigLessThan.b) |] _ n).
Proof.
  exact BigLessThan.soundness.
Qed.

(* BigAddModP *)
Theorem BigAddModP_Soundness {n k: nat}: forall (c: @BigAddModP.t n k),
  (* pre-conditions *)
  0 < n ->
  0 < k ->
  n + 2 <= C.k ->
  'c.(BigAddModP.a) |: (n) ->
  'c.(BigAddModP.b) |: (n) ->
  'c.(BigAddModP.p) |: (n) ->
  [|'c.(BigAddModP.a)|] _ n <= [|'c.(BigAddModP.p)|] _ n - 1 ->
  [|'c.(BigAddModP.b)|] _ n <= [|'c.(BigAddModP.p)|] _ n - 1 ->
  (* post-conditions *)
  [|'c.(BigAddModP.out)|] _ n = ([|'c.(BigAddModP.a)|] _ n + [|'c.(BigAddModP.b)|] _ n) mod [|'c.(BigAddModP.p)|] _ n /\ 
  'c.(BigAddModP.out) |: (n).
Proof.
  exact BigAddModP.soundness.
Qed.

(* BigSubModP *)
Theorem BigSubModP_Soundness {n k: nat}: forall (c: @BigSubModP.t n k),
  0 < n ->
  0 < k ->
  n + 2 <= C.k ->
  'c.(BigSubModP.a) |: (n) ->
  'c.(BigSubModP.b) |: (n) ->
  'c.(BigSubModP.p) |: (n) ->
  [|'c.(BigSubModP.a)|] _ n <= [|'c.(BigSubModP.p)|] _ n - 1 ->
  [|'c.(BigSubModP.b)|] _ n <= [|'c.(BigSubModP.p)|] _ n - 1 ->
  [|'c.(BigSubModP.out)|] _ n = 
  ([|'c.(BigSubModP.a)|] _ n - [|'c.(BigSubModP.b)|] _ n) mod [|'c.(BigSubModP.p)|] _ n 
  /\ 
  'c.(BigSubModP.out) |: (n).
Proof.
  exact BigSubModP.soundness.
Qed.

(* CheckCarryToZero *)
(* Theorem CheckCarryToZero_Soundness {n m k: nat}: forall (c: @CheckCarryToZero.t n m k), 
  1 <= n <= m ->
  2 <= k ->
  m < r ->
  'c.(CheckCarryToZero._in) |: (m) ->
  'c.(CheckCarryToZero._in) |: (n) ->
  [| 'c.(CheckCarryToZero._in) |] _ n = 0%Z.
Proof.
  exact CheckCarryToZero.soundness.
Qed. *)

(* Split *)
Theorem Split_Soundness {n m: nat}: forall (c: @Split.t n m), 
  exists (small_b: F^n) (big_b: F^m),
  Repr.repr_le2 c.(Split.small) n ('small_b) /\
  Repr.repr_le2 c.(Split.big) m ('big_b) /\
  c.(Split._in) = c.(Split.small) + c.(Split.big) * 2^n.
Proof.
  exact Split.soundness.
Qed.

(* SplitThree *)
Theorem SplitThree_Soundness {n m k: nat}: forall (c: @SplitThree.t n m k), 
  exists (small_b: F^n) (medium_b: F^m) (big_b: F^k),
  Repr.repr_le2 c.(SplitThree.small) n ('small_b) /\
  Repr.repr_le2 c.(SplitThree.medium) m ('medium_b) /\
  Repr.repr_le2 c.(SplitThree.big) k ('big_b) /\
  c.(SplitThree._in) = c.(SplitThree.small) + c.(SplitThree.medium) * 2^n + c.(SplitThree.big) * 2^(n+m).
Proof.
  exact SplitThree.soundness.
Qed.

(* BigMod *)
Theorem BigMod_Soundness {n k: nat}: forall (c: @BigMod.t n k), 
  0 < n ->
  0 < k ->
  n + 2 <= C.k ->
  'c.(BigMod.a) |: (n) ->
  'c.(BigMod.b) |: (n) ->
  'c.(BigMod.div) |: (n) /\
  'c.(BigMod._mod) |: (n) /\
  ([|'c.(BigMod.a)|] _ n = [|'c.(BigMod.div)|] _ n * [|'c.(BigMod.b)|] _ n + [|'c.(BigMod._mod)|] _ n)%Z.
Proof.
  exact BigMod.soundness.
Qed.

(* To Add: BigMultNoCarry *)

(* TODO: BigMult *)