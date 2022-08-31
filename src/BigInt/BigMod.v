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
From Circom.CircomLib Require Import Bitify.
From Circom.BigInt Require Import BigAdd BigMult BigLessThan.

(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module BigMod.

Module B := Bitify.
Module D := DSL.
Module Cmp := Comparators.
Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.
Module R := Repr.
Module Add := BigAdd.
Module Mult := BigMult.
Module LessThan := BigLessThan.
Import B.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Section _BigMod.
Context {n k: nat}.

(* // leading register of b should be non-zero
template BigMod(n, k) {
    signal input a[2 * k];
    signal input b[k];

    signal output div[k + 1];
    signal output mod[k];

    component range_checks[k + 1];
    for (var i = 0; i <= k; i++) {
        range_checks[i] = Num2Bits(n);
        range_checks[i].in <== div[i];
    }

    component mul = BigMult(n, k + 1);
    for (var i = 0; i < k; i++) {
        mul.a[i] <== div[i];
        mul.b[i] <== b[i];
    }
    mul.a[k] <== div[k];
    mul.b[k] <== 0;

    component add = BigAdd(n, 2 * k + 2);
    for (var i = 0; i < 2 * k; i++) {
        add.a[i] <== mul.out[i];
        if (i < k) {
            add.b[i] <== mod[i];
        } else {
            add.b[i] <== 0;
        }
    }

    add.a[2 * k] <== mul.out[2 * k];
    add.a[2 * k + 1] <== mul.out[2 * k + 1];
    add.b[2 * k] <== 0;
    add.b[2 * k + 1] <== 0;

    for (var i = 0; i < 2 * k; i++) {
        add.out[i] === a[i];
    }
    add.out[2 * k] === 0;
    add.out[2 * k + 1] === 0;

    component lt = BigLessThan(n, k);
    for (var i = 0; i < k; i++) {
        lt.a[i] <== mod[i];
        lt.b[i] <== b[i];
    }
    lt.out === 1;
} *)

Definition cons (a: F^(2 * k)) (b: F^k) (div: F^(k+1)) (_mod: F^k) :=
  exists (range_checks: (@Num2Bits.t n) ^ (k + 1)) 
         (mul: @Mult.t (k+1)%nat) (add: @Add.t n (2 * k + 2)) 
         (lt: @LessThan.t n k),
  (* range check for div *)
  D.iter (fun (i: nat) (_cons: Prop) => _cons /\
    range_checks[i].(Num2Bits._in) = div[i]) (k+1) True /\
  (* mul *)
  D.iter (fun (i: nat) (_cons: Prop) => _cons /\
    mul.(Mult.a)[i] = div[i] /\
    mul.(Mult.b)[i] = b[i]) k True /\
  mul.(Mult.a)[k] = div[k] /\
  mul.(Mult.b)[k] = 0 /\
  (* add *)
  D.iter (fun (i: nat) (_cons: Prop) => _cons /\
    add.(Add.a)[i] = mul.(Mult.out)[i] /\
    if (i < k)? then
      add.(Add.b)[i] = _mod[i]
    else
      add.(Add.b)[i] = 0) (2 * k) True /\
  add.(Add.a)[2 * k] = mul.(Mult.out)[2 * k] /\
  add.(Add.a)[2 * k + 1] = mul.(Mult.out)[2 * k + 1] /\
  add.(Add.b)[2 * k] = 0 /\
  add.(Add.b)[2 * k + 1] = 0 /\
  (* a and add.out *)
  D.iter (fun (i: nat) (_cons: Prop) => _cons /\
    add.(Add.out)[i] = a[i]) (2 * k) True /\
  add.(Add.out)[2 * k] = 0 /\
  add.(Add.out)[2 * k + 1] = 0 /\
  (* less than *)
  D.iter (fun (i: nat) (_cons: Prop) => _cons /\
    lt.(LessThan.a)[i] = _mod[i] /\
    lt.(LessThan.b)[i] = b[i]) k True /\
  lt.(LessThan.out) = 1
.

Record t := { a: F^(2 * k); b: F^k; div: F^(k+1); _mod: F^k; _cons: cons a b div _mod }.
Local Notation "[| xs |]" := (RZ.as_le n xs).

(* Lemma firstn_congruence: forall i *)
Local Notation "xs !! i" := (List.nth i xs _) (at level 10).

Create HintDb DSL discriminated.

#[local]Hint Extern 10 (_ < _) => lia : core.
#[local]Hint Extern 10 (_ <= _) => lia : core.
#[local]Hint Extern 10 (_ > _) => lia : core.
#[local]Hint Extern 10 (_ >= _) => lia : core.
#[local]Hint Extern 10 (_ = _) => lia : core.

Ltac pose_as_le_nonneg := repeat match goal with
| [ |- context[RZ.as_le ?n ?xs ] ] =>
  let t := type of (RZ.as_le_nonneg n xs) in
  lazymatch goal with
  (* already posed *)
  | [ _: t |- _] => fail
  | _ => 
    let Hnonneg := fresh "_Hnonneg" in
    pose proof (RZ.as_le_nonneg n xs) as Hnonneg
    ;move Hnonneg at top
  end
| _ => fail
end.

Ltac rewrite_length :=
  repeat match goal with
  | [ H: length ?xs = ?l |- context[length ?xs] ] =>
    rewrite H
  | [ H: length ?xs = ?l, H': context[length ?xs] |- _] =>
    rewrite H in H'
  end.

Ltac lrewrite :=
  repeat match goal with
  | [ H: ?x = _ |- context[?x] ] => rewrite H
  end.
Ltac rrewrite :=
  repeat match goal with
  | [ H: _ = ?x |- context[?x] ] => rewrite H
  end.

Theorem soundness: forall (c: t),
  0 < n ->
  0 < k ->
  n + 2 <= C.k ->
  'c.(a) |: (n) ->
  'c.(b) |: (n) ->
  'c.(div) |: (n) ->
  'c.(_mod) |: (n) ->
  ([|'c.(a)|] = [|'c.(div)|] * [|'c.(b)|] + [|'c.(_mod)|])%Z.
Proof.
  unwrap_C.
  intros c Hn Hk Hnk Ha Hb Hdiv Hmod.
  destruct c as [a b div _mod [range_checks [mul [add [lt prog]]]]].
  simpl in *.
  destruct prog as [Prange [Pmul [Pmul1 [Pmul2 [Padd [Padd1 [Padd2 [Padd3 [Padd4 [Pa [Pa1 [Pa2 [Plt Plt1]]]]]]]]]]]]].
  pose_lengths.
  rem_iter.
Abort.

End _BigMod.
End BigMod.