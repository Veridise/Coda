Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.Znumtheory.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.


Require Import Circom.Tuple.
Require Import Crypto.Util.Decidable Crypto.Util.Notations.
Require Import BabyJubjub.
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Crypto.Algebra.Ring Crypto.Algebra.Field.

Require Import Util.

(* Circuit:
* https://github.com/iden3/circomlib/blob/master/circuits/gates.circom
*)

Local Open Scope list_scope.
Local Open Scope F_scope.

Section Gates.

Context {F eq zero one opp add sub mul inv div}
        {fld:@Hierarchy.field F eq zero one opp add sub mul inv div}
        {eq_dec:DecidableRel eq}.
Local Infix "=" := eq. Local Notation "a <> b" := (not (a = b)).
Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
Local Notation "0" := zero.  Local Notation "1" := one.
Local Infix "+" := add. Local Infix "*" := mul.
Local Infix "-" := sub. Local Infix "/" := div.

Ltac split_eqns :=
  repeat match goal with
  | [ |- _ /\ _ ] => split
  | [ H: exists _, _ |- _ ] => destruct H
  | [ H: {s | _ } |- _ ] => destruct H
  | [ H: _ /\ _ |- _ ] => destruct H
  end.

(* template XOR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - 2*a*b;
} *)

(* XOR template *)

Definition XOR a b out:=
  out = a + b - (1 + 1) * a * b.

(* XOR spec *)
Definition XOR_spec a b out :=
  (a = 0 /\ b = 0 -> out = 0) /\
  (a = 0 /\ b = 1 -> out = 1) /\
  (a = 1 /\ b = 0 -> out = 1) /\
  (a = 1 /\ b = 1 -> out = 0).

(* XOR correctness theorem *)
Theorem XOR_correct: forall a b out,
  XOR a b out -> XOR_spec a b out.
Proof using Type*.
  intros.
  unfold XOR, XOR_spec in *.
  repeat (split_eqns; intro); inversion H0; fsatz.
Qed.

(* template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
} *)

(* AND template *)

Definition AND a b out:=
  out = a * b.

(* AND spec *)
Definition AND_spec a b out :=
  (a = 0 /\ b = 0 -> out = 0) /\
  (a = 0 /\ b = 1 -> out = 0) /\
  (a = 1 /\ b = 0 -> out = 0) /\
  (a = 1 /\ b = 1 -> out = 1).

(* AND correctness theorem *)
Theorem AND_correct: forall a b out,
  AND a b out -> AND_spec a b out.
Proof using Type*.
  intros.
  unfold AND, AND_spec in *.
  repeat (split_eqns; intro); inversion H0; fsatz.
Qed.

(* template OR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - a*b;
} *)

(* OR template *)

Definition OR a b out:=
  out = a + b - a*b.

(* OR spec *)
Definition OR_spec a b out :=
  (a = 0 /\ b = 0 -> out = 0) /\
  (a = 0 /\ b = 1 -> out = 1) /\
  (a = 1 /\ b = 0 -> out = 1) /\
  (a = 1 /\ b = 1 -> out = 1).

(* OR correctness theorem *)
Theorem OR_correct: forall a b out,
  OR a b out -> OR_spec a b out.
Proof using Type*.
  intros.
  unfold OR, OR_spec in *.
  repeat (split_eqns; intro); inversion H0; fsatz.
Qed.

(* template NOT() {
    signal input in;
    signal output out;

    out <== 1 + in - 2*in;
} *)

(* NOT template *)

Definition NOT _in out:=
  out = 1 + _in - (1+1)*_in.

(* NOT spec *)
Definition NOT_spec _in out :=
  (_in = 0 -> out = 1) /\
  (_in = 1 -> out = 0).

(* NOT correctness theorem *)
Theorem NOT_correct: forall _in out,
  NOT _in out -> NOT_spec _in out.
Proof using Type*.
  intros.
  unfold NOT, NOT_spec in *.
  repeat (split_eqns; intro); fsatz.
Qed.

(* template NAND() {
    signal input a;
    signal input b;
    signal output out;

    out <== 1 - a*b;
} *)

(* NAND template *)

Definition NAND a b out:=
  out = 1 - a*b.

(* NAND spec *)
Definition NAND_spec a b out :=
  (a = 0 /\ b = 0 -> out = 1) /\
  (a = 0 /\ b = 1 -> out = 1) /\
  (a = 1 /\ b = 0 -> out = 1) /\
  (a = 1 /\ b = 1 -> out = 0).

(* NAND correctness theorem *)
Theorem NAND_correct: forall a b out,
  NAND a b out -> NAND_spec a b out.
Proof using Type*.
  intros.
  unfold NAND, NAND_spec in *.
  repeat (split_eqns; intro); inversion H0; fsatz.
Qed.

(* template NOR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b + 1 - a - b;
} *)

(* NOR template *)

Definition NOR a b out:=
  out = a*b + 1 - a - b.

(* NOR spec *)
Definition NOR_spec a b out :=
  (a = 0 /\ b = 0 -> out = 1) /\
  (a = 0 /\ b = 1 -> out = 0) /\
  (a = 1 /\ b = 0 -> out = 0) /\
  (a = 1 /\ b = 1 -> out = 0).

(* NOR correctness theorem *)
Theorem NOR_correct: forall a b out,
  NOR a b out -> NOR_spec a b out.
Proof using Type*.
  intros.
  unfold NOR, NOR_spec in *.
  repeat (split_eqns; intro); inversion H0; fsatz.
Qed.

(* template MultiAND(n) {
    signal input in[n];
    signal output out;
    component and1;
    component and2;
    component ands[2];
    if (n==1) {
        out <== in[0];
    } else if (n==2) {
        and1 = AND();
        and1.a <== in[0];
        and1.b <== in[1];
        out <== and1.out;
    } else {
        and2 = AND();
        var n1 = n\2;
        var n2 = n-n\2;
        ands[0] = MultiAND(n1);
        ands[1] = MultiAND(n2);
        var i;
        for (i=0; i<n1; i++) ands[0].in[i] <== in[i];
        for (i=0; i<n2; i++) ands[1].in[i] <== in[n1+i];
        and2.a <== ands[0].out;
        and2.b <== ands[1].out;
        out <== and2.out;
    }
} *)

(* MultiAND(n) TODO *)

End Gates.