Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.
Require Import Coq.ZArith.Znat.


Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Arithmetic.PrimeFieldTheorems.

Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Ring.


From Circom Require Import Circom Default Util DSL Tuple ListUtil LibTactics Simplify.
From Circom Require Import Signed.


Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Local Open Scope Z_scope.

Lemma lt_pow_lt_half: forall x,
x < 2^(C.k-1) -> x < q//2.
Proof.
intros. pose proof Signed.half_lb.
lia.
Qed.

Lemma mul_r_pow_lt_pow: forall x m n,
0 <= n <= m ->
x < 2^(m-n) -> x * 2^n < 2^m.
Proof.
intros.
Admitted.

Lemma mul_r_pow_le_pow: forall x m n,
0 <= n <= m ->
x <= 2^(m-n) -> x * 2^n <= 2^m.
Proof.
intros.
Admitted.

Lemma mul_l_pow_lt_pow: forall x m n,
0 <= n <= m ->
x < 2^(m-n) -> 2^n * x < 2^m.
Proof.
intros.
Admitted.

Lemma mul_l_pow_le_pow: forall x m n,
0 <= n <= m ->
x <= 2^(m-n) -> 2^n * x <= 2^m.
Proof.
intros.
Admitted.

Lemma pow_cut_le_lt: forall x m n,
0 <= m ->
0 <= n ->
m < n ->
x <= 2^m ->
x < 2^n.
Admitted.

Lemma pow_cut_le: forall x m n,
0 <= m ->
0 <= n ->
m <= n ->
x <= 2^m ->
x <= 2^n.
Admitted.


Lemma lt_split_half_left: forall x y m,
x < 2^(m-1) ->
y <= 2^(m-1) ->
x + y < 2^m.
Admitted.

Lemma lt_split_half_right: forall x y m,
x <= 2^(m-1) ->
y < 2^(m-1) ->
x + y < 2^m.
Admitted.

Ltac abs :=
  repeat match goal with
  | [ |- context[Z.abs (?b^?m * ?x)%Z] ] => rewrite Z.abs_mul with (n:=(b^m)%Z)
  | [ |- context[Z.abs (?x * ?b^?m)%Z] ] => rewrite Z.abs_mul with (m:=(b^m)%Z)
  | [ |- context[Z.abs (?b^?m)%Z] ] => rewrite Z.abs_eq with (n:=(b^m)%Z)
  end.

Ltac overflow n :=
abs;
try lia;
match n with
| S ?n' =>
  match goal with
  | [ |- _ < q//2 ] => apply lt_pow_lt_half; overflow n'
  | [ |- _ * 2^_ < 2^_] => apply mul_r_pow_lt_pow; overflow n'
  | [ |- 2^_ * _ < 2^_] => apply mul_l_pow_lt_pow; overflow n'
  | [ |- _ * 2^_ <= 2^_] => apply mul_r_pow_le_pow; overflow n'
  | [ |- 2^_ * _ <= 2^_] => apply mul_l_pow_le_pow; overflow n'
  | [ _: ?x <= 2^?k |- ?x < 2^_ ] => apply pow_cut_le_lt with (m:=k); overflow n'
  | [ _: ?x <= 2^?k |- ?x <= 2^_ ] => apply pow_cut_le with (m:=k); overflow n'
  | [ |- _ + _ < 2^_ ] => 
    (apply lt_split_half_left; overflow n') || 
    (apply lt_split_half_right; overflow n')
  | _ => idtac "no match"; fail 1
  end
| _ => idtac "done"
end.