Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems Crypto.Algebra.Field.


Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Decidable Crypto.Util.Notations.
Require Import BabyJubjub.
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Ring.

Require Import Util.


(* Require Import Crypto.Spec.ModularArithmetic. *)
(* Circuit:
* https://github.com/0xPARC/circom-ecdsa/blob/08c2c905b918b563c81a71086e493cb9d39c5a08/circuits/bigint.circom
*)

Section _bitify.

Local Open Scope list_scope.
Local Open Scope F_scope.

Ltac fqsatz := fsatz_safe; autorewrite with core; auto.

Context (q:positive) (k:Z) {prime_q: prime q} {two_lt_q: 2 < q} {k_positive: 1 < k} {q_lb: 2^k < q}.

Lemma q_gtb_1: (1 <? q)%positive = true.
Proof.
  apply Pos.ltb_lt. lia.
Qed.

Lemma q_gt_2: 2 < q.
Proof.
  replace 2%Z with (2^1)%Z by lia.
  apply Z.le_lt_trans with (m := (2 ^ k)%Z); try lia.
  eapply Zpow_facts.Zpower_le_monotone; try lia.
Qed.

Hint Rewrite q_gtb_1 : core.

(**************************
 * Overflow Representation
 **************************)
Definition two : F q := 1 + 1.
Notation "2" := two.

Lemma to_Z_2: F.to_Z 2 = 2%Z.
Proof. simpl. repeat rewrite Z.mod_small; lia. Qed.


(* peel off 1 from x^(i+1) in field exp *)
Lemma pow_S_N: forall (x: F q) i,
  x ^ (N.of_nat (S i)) = x * x ^ (N.of_nat i).
Proof.
  intros.
  replace (N.of_nat (S i)) with (N.succ (N.of_nat i)).
  apply F.pow_succ_r.
  induction i.
  - reflexivity.
  - simpl. f_equal.
Qed.

(* peel off 1 from x^(i+1) in int exp *)
Lemma pow_S_Z: forall (x: Z) i,
  (x ^ (Z.of_nat (S i)) = x * x ^ (Z.of_nat i))%Z.
Proof.
  intros.
  replace (Z.of_nat (S i)) with (Z.of_nat i + 1)%Z by lia.
  rewrite Zpower_exp; lia.
Qed.

(* [repr]esentation [func]tion:
 * interpret a list of weights as representing a little-endian base-2^n number
 *)
Fixpoint repr_to_le' (n: nat) (i: nat) (ws: list (F q)) : F q :=
  match ws with
  | nil => 0
  | w::ws' => w * two^(N.of_nat n * N.of_nat i) + repr_to_le' n (S i) ws'
  end.

Definition repr_to_le n := repr_to_le' n 0%nat.

(* repr func lemma: single-step index change *)
Lemma repr_to_le'_S: forall ws n i,
  repr_to_le' n (S i) ws = 2^(N.of_nat n) * repr_to_le' n i ws.
Proof.
  induction ws as [| w ws]; intros.
  - fqsatz.
  - cbn [repr_to_le'].
    rewrite IHws.
    remember (N.of_nat n) as m.
    replace (2^(m * N.of_nat (S i))) with (2^m * 2 ^ (m * N.of_nat i)).
    fqsatz.
    rewrite <- F.pow_add_r. f_equal. lia.
Qed.

(* Probably not needed
(* repr func lemma: multi-step index change *)
Lemma repr_to_le'_n: forall ws i j,
  repr_to_le' (i+j) ws = 2^(N.of_nat i) * repr_to_le' j ws.
Proof.
  induction i; intros; simpl.
  - rewrite F.pow_0_r. fqsatz.
  - rewrite repr_to_le'_S. rewrite IHi.
    replace (N.pos (Pos.of_succ_nat i)) with (1 + N.of_nat i)%N.
    rewrite F.pow_add_r.
    rewrite F.pow_1_r.
    fqsatz.
    lia.
Qed. *)

(* repr func lemma: decomposing weight list *)
Lemma repr_to_le_app: forall ws2 ws1 ws n i,
  ws = ws1 ++ ws2 ->
  repr_to_le' n i ws = repr_to_le' n i ws1 + repr_to_le' n (i + length ws1) ws2.
Proof.
  induction ws1; simpl; intros.
  - subst. replace (i+0)%nat with i by lia. fqsatz.
  - destruct ws; inversion H; subst.
    simpl.
    assert (repr_to_le' n (S i) (ws1 ++ ws2) = 
      repr_to_le' n (S i) ws1 + repr_to_le' n (i + S (length ws1)) ws2). {
        rewrite <- plus_n_Sm, <- plus_Sn_m.
        eapply IHws1. reflexivity.
      }
    fqsatz.
Qed.

Definition half: Z. Admitted.
Notation "r//2" := half.

(* To signed integer *)
Definition toSZ (x: F q) := let z := F.to_Z x in
  if z >=? r//2 + 1 then (z-q)%Z else z.


(* overflow representation *)
(* FIXME: repr_to_le' should call toSZ *)
Definition repr_overflow x l n ws :=
  length ws = l /\
  x = repr_to_le' n 0%nat ws.


  (* Definition Num2Bits (n: nat) (_in: F q) (_out: tuple (F q) n) : Prop :=
  let lc1 := 0 in
  let e2 := 1 in
  let '(lc1, e2, _C) := (iter n (fun (i: nat) '(lc1, e2, _C) =>
    let out_i := (Tuple.nth_default 0 i _out) in
      (lc1 + out_i * e2,
      e2 + e2,
      (out_i * (out_i - 1) = 0) /\ _C))
    (lc1, e2, True)) in
  (lc1 = _in) /\ _C. *)
Locate nth_default.

Notation "x [ i ]" := (Tuple.nth_default 0 i x).

Definition BigMultNoCarry_cons
  ka kb
  (a: tuple (F q) ka)
  (b: tuple (F q) kb)
  (out: tuple (F q) (ka + kb - 1))
  (a_poly: tuple (F q) (ka+ kb -1))
  (b_poly: tuple (F q) (ka+ kb -1))
  (out_poly: tuple (F q) (ka+ kb -1)) :=
  let _C := True in
  let '(out_poly, _C) :=
    (* outer loop: construct out_poly[i] *)
    iter (ka+kb-1) (fun i '(out_poly, _C) => (out_poly, _C /\
        (* inner loop: sum out[j] * i ** j *)
        out_poly[i] = iter (ka+kb-1) (fun j out_poly_i =>
          (out_poly_i + out[j] * (F.of_nat q i)^(N.of_nat j))) 0))
      (out_poly, _C) in
  let '(a_poly, _C) :=
    (* outer loop: construct a_poly[i] *)
    iter (ka+kb-1) (fun i '(a_poly, _C) => (a_poly, _C /\
        (* inner loop: sum a[j] * i ** j *)
        a_poly[i] = iter (ka) (fun j a_poly_i =>
          (a_poly_i + a[j] * (F.of_nat q i)^(N.of_nat j))) 0))
      (a_poly, _C) in
  let '(b_poly, _C) :=
    (* outer loop: construct b_poly[i] *)
    iter (ka+kb-1) (fun i '(b_poly, _C) => (b_poly, _C /\
        (* inner loop: sum a[j] * i ** j *)
        b_poly[i] = iter (kb) (fun j b_poly_i =>
          (b_poly_i + a[j] * (F.of_nat q i)^(N.of_nat j))) 0))
      (b_poly, _C) in
  let _C :=
    iter (ka+kb-1) (fun i _C => _C /\ 
      out_poly[i] = a_poly[i] * b_poly[i]) _C in
  _C.

Definition BigMultNoCarry
  ka kb
  (a: tuple (F q) ka)
  (b: tuple (F q) kb)
  (out: tuple (F q) (ka + kb - 1)) :=
  exists a_poly b_poly out_poly, 
    BigMultNoCarry_cons ka kb a b out a_poly b_poly out_poly.



