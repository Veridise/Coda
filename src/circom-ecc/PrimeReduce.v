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
Require Import Circom.circomlib.bitify.

Require Import Crypto.Spec.ModularArithmetic.
(* Circuit:
* https://github.com/0xPARC/circom-ecdsa/blob/08c2c905b918b563c81a71086e493cb9d39c5a08/circuits/bigint.circom
*)

Section _bigint.

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

Notation "x [ i ]" := (Tuple.nth_default 0 i x).

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

(* 
(* overflow representation *)
(* interpret a list of weights as representing a little-endian base-2^n number *)
Fixpoint repr_to_le_Z' (n: nat) (i: nat) (ws: list (F q)) : Z :=
  match ws with
  | nil => 0
  | w::ws' => (toSZ w) * 2^(N.of_nat n * N.of_nat i) + repr_to_le_Z' n (S i) ws'
  end.

(* overflow representation *)
(* FIXME: repr_to_le' should call toSZ *)
Definition repr_overflow x l n ws :=
  length ws = l /\
  x = repr_to_le_Z' n 0%nat ws. *)


Definition half: Z. exact (Z.div q 2). Defined.
Notation "r//2" := half.

(* To signed integer *)
Definition toSZ (x: F q) := let z := F.to_Z x in
  if z >=? r//2 + 1 then (z-q)%Z else z.

Lemma toSZ_add: forall a b,
  Z.abs (toSZ a) + Z.abs (toSZ b) < r//2 ->
  toSZ (a + b) = (toSZ a + toSZ b)%Z.
Proof. Abort.

Lemma toSZ_mult: forall a b,
  Z.abs (toSZ a) * Z.abs (toSZ b) < r//2 ->
  toSZ (a * b) = (toSZ a * toSZ b)%Z.
Proof. Abort.

(* PrimeReduce *)
(* source: https://github.com/yi-sun/circom-pairing/blob/743d761f07254ea6407d29ba05f29886cfd14aec/circuits/bigint.circom#L786 *)

(* source: https://github.com/yi-sun/circom-pairing/blob/743d761f07254ea6407d29ba05f29886cfd14aec/circuits/bigint_func.circom *)

Definition F_mod {m} (a b: F m) :=
  F.of_Z m ((F.to_Z a) mod (F.to_Z b))%Z.

(* // a is a n-bit scalar
// b has k registers
function long_scalar_mult(n, k, a, b) {
    var out[50];
    for (var i = 0; i < 50; i++) {
        out[i] = 0;
    }
    for (var i = 0; i < k; i++) {
        var temp = out[i] + (a * b[i]);
        out[i] = temp % (1 << n);
        out[i + 1] = out[i + 1] + temp \ (1 << n);
    }
    return out;
} *)
Definition long_scalar_mult
n k a (_b : tuple (F q) k) (out : tuple (F q) 50) :=
let _C := True in
let '( _C) :=
  (* loop: construct out[i] *)
  iter 50 (fun i '( _C) => (_C /\ out[i] = 0))
    ( _C) in
let '( _C) :=
  iter k (fun i _C => _C /\ 
              out[i] = F_mod (out[i] + (a * _b[i]))  (2^n) /\
              out[i + 1] = out[i + 1] + F.div (out[i] + (a * _b[i])) (2^n))
    _C in
  _C
.

(* // n bits per register
// a has k registers
// b has k registers
// a >= b
function long_sub(n, k, a, b) {
    var diff[50];
    var borrow[50];
    for (var i = 0; i < k; i++) {
        if (i == 0) {
           if (a[i] >= b[i]) {
               diff[i] = a[i] - b[i];
               borrow[i] = 0;
            } else {
               diff[i] = a[i] - b[i] + (1 << n);
               borrow[i] = 1;
            }
        } else {
            if (a[i] >= b[i] + borrow[i - 1]) {
               diff[i] = a[i] - b[i] - borrow[i - 1];
               borrow[i] = 0;
            } else {
               diff[i] = (1 << n) + a[i] - b[i] - borrow[i - 1];
               borrow[i] = 1;
            }
        }
    }
    return diff;
} *)
Definition long_sub (n : nat) (_k : nat) (a b : tuple (F q) _k) : tuple (F q) 50.
Admitted.

(* // 1 if true, 0 if false
function long_gt(n, k, a, b) {
    for (var i = k - 1; i >= 0; i--) {
        if (a[i] > b[i]) {
            return 1;
        }
        if (a[i] < b[i]) {
            return 0;
        }
    }
    return 0;
} *)
Definition long_gt (n : nat) (_k : nat) (a b : tuple (F q) _k) : F q.
Admitted.

(* // n bits per register
// a has k + 1 registers
// b has k registers
// assumes leading digit of b is at least 2^(n - 1)
// 0 <= a < (2**n) * b
function short_div_norm(n, k, a, b) {
   var qhat = (a[k] * (1 << n) + a[k - 1]) \ b[k - 1];
   if (qhat > (1 << n) - 1) {
      qhat = (1 << n) - 1;
   }

   var mult[50] = long_scalar_mult(n, k, qhat, b);
   if (long_gt(n, k + 1, mult, a) == 1) {
      mult = long_sub(n, k + 1, mult, b);
      if (long_gt(n, k + 1, mult, a) == 1) {
         return qhat - 2;
      } else {
         return qhat - 1;
      }
   } else {
       return qhat;
   }
} *)
Definition short_div_norm (n : nat) (_k : nat) (a : tuple (F q) (_k + 1)) (b : tuple (F q) _k) : F q.
Admitted.

(* // n bits per register
// a has k + 1 registers
// b has k registers
// assumes leading digit of b is non-zero
// 0 <= a < b * 2^n
function short_div(n, k, a, b) {
    var scale = (1 << n) \ (1 + b[k - 1]);
    // k + 2 registers now
    var norm_a[50] = long_scalar_mult(n, k + 1, scale, a);
    // k + 1 registers now
    var norm_b[50] = long_scalar_mult(n, k, scale, b);
    
    var ret;
    if (norm_b[k] != 0) {
	ret = short_div_norm(n, k + 1, norm_a, norm_b);
    } else {
	ret = short_div_norm(n, k, norm_a, norm_b);
    }
    return ret;
}*)
Definition short_div (n : nat) (_k : nat) (a : tuple (F q) (_k + 1)) (b : tuple (F q) _k) : F q.
Admitted.

(* // n bits per register
// a has k + m registers
// b has k registers
// out[0] has length m + 1 -- quotient
// out[1] has length k -- remainder
// implements algorithm of https://people.eecs.berkeley.edu/~fateman/282/F%20Wright%20notes/week4.pdf
// b[k-1] must be nonzero! *)
Definition long_div2 (n : nat) (_k m : nat) (a : tuple (F q) (_k + m)) (b : tuple (F q) _k) : tuple (F q) 2.
Admitted.

Definition long_div := long_div2.

(* function SplitThreeFn(in, n, m, k) {
    return [in % (1 << n), (in \ (1 << n)) % (1 << m), (in \ (1 << n + m)) % (1 << k)];
} *)

Definition SplitThreeFn _in n m k (out : tuple (F q) 3):=
  out[0] = F_mod _in (2^n) /\
  out[1] = F_mod (F.div _in (2^n)) (2^m) /\
  out[2] = F_mod (F.div _in (2^n + (F.of_Z q m))) (2^k).
   

(* function SplitFn(in, n, m) {
    return [in % (1 << n), (in \ (1 << n)) % (1 << m)];
} *)
Definition SplitFn _in n m (out : tuple (F q) 2):=
  out[0] = F_mod _in (2^n) /\
  out[1] = F_mod (F.div _in (2^n)) (2^m).

(* // n bits per register
// a and b both have k registers
// out[0] has length 2 * k
// adapted from BigMulShortLong and LongToShortNoEndCarry witness computation *)
Definition prod (n : nat) (_k : nat) (a : tuple (F q) _k) (b : tuple (F q) _k) : tuple (F q) 50.
Admitted.

(* function prod_mod(n, k, a, b, p) {
    var prod[50] = prod(n,k,a,b);
    var temp[2][50] = long_div(n,k,prod,p);
    return temp[1];
} *)
Definition prod_mod {_k1 _k2 _k3}(n : nat) (_k : nat) (a : tuple (F q) _k1) (b: tuple (F q) _k2) (p: tuple (F q) _k3): tuple (F q) 50.
Admitted.

Definition repr_binary n x m ws :=
  length ws = m /\
  (forall i, (i < m)%nat -> binary q (nth i ws 0)) /\
  x = repr_to_le n ws.

Hypothesis prod_mod_correct:
  forall (n: nat) k (a b p: tuple (F q) k),
  repr_binary n (F_mod ((repr_to_le n (to_list k a)) * (repr_to_le n (to_list k b))) (repr_to_le n (to_list k p))) 50
  (to_list 50 (prod_mod n k a b p)).

(* // n bits per register
// a has k registers
// p has k registers
// e has k registers
// k * n <= 500
// p is a prime
// computes a^e mod p *)
Definition mod_exp {_k1 _k2 _k3} (n: nat) (_k: nat) (a : tuple (F q) _k1) (p : tuple (F q) _k2) (e : tuple (F q) _k3) : tuple (F q) 50. Admitted.

Hypothesis mod_exp_correct:
  forall (n: nat) k (a p e : tuple (F q) k),
  repr_binary n (F_mod ((repr_to_le n (to_list k a)) ^ (F.to_N (repr_to_le n (to_list k e))))
                        (repr_to_le n (to_list k p))) 50
  (to_list 50 (mod_exp n k a p e)).

(* k < 2^n *)
Definition PrimeReduce_cons
  n k m (p : tuple (F q) k)
  (_in : tuple (F q) (m+k))
  (_out : tuple (F q) k)
  (two : tuple (F q) k)
  (e_1 : tuple (F q) k)
  (e_2 : tuple (F q) k)
  (_r : tuple (tuple (F q) 50) m)
  (out_sum : tuple (F q) k)
   :=
  let _C := two[0] = 2 /\ e_1[0] = (F.of_nat q n) /\ e_2[0] = (F.of_nat q k) in
  let _C :=
    iter' (Nat.sub k 1) k (fun i _C => _C /\ 
      two[i] = 0 /\ e_1[i] = 0 /\ e_2[i] = 0) _C in
  let pow2n := mod_exp n k two p e_1 in
  let pow2nk := mod_exp n k pow2n p e_2 in
  let _C :=
    iter' (Nat.sub m 1) m (fun i _C => _C /\ 
          (nth_default (repeat 0 50) i _r) = prod_mod n k (nth_default (repeat 0 50) (i-1) _r) pow2n p) 
          ((nth_default (repeat 0 50) 0 _r) = pow2nk /\ _C) in
  let _C :=
    iter k (fun i _C => _C /\ 
      out_sum[i] = _in[i]) _C in
  let _C :=
    iter m (fun i _C => _C /\ 
      (iter k (fun j _C => _C /\ 
                  out_sum[j] = out_sum[j] + _in[i+k] * (nth_default (repeat 0 50) i _r)[j]) _C)) _C in
  let _C :=
    iter k (fun i _C => _C /\ 
      _out[i] = out_sum[i]) _C in
  _C
  .

Definition PrimeReduce n k m p _in _out :=
  exists two e_1 e_2 _r out_sum,
  PrimeReduce_cons n k m p _in _out two e_1 e_2 _r out_sum.

Definition PrimeReduce_spec n k m (p : tuple (F q) k) (_in : tuple (F q) (m+k)) (_out : tuple (F q) k) :=
  F_mod (repr_to_le n (toPoly _in)) (repr_to_le n (toPoly p)) = 
  F_mod (repr_to_le n (toPoly _out)) (repr_to_le n (toPoly p)).

Theorem PrimeReduce_correct n _k m p _in _out:
  PrimeReduce n _k m p _in _out -> PrimeReduce_spec n _k m p _in _out.
Proof.
Admitted.