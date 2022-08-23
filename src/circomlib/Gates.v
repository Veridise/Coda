Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.Znumtheory.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Coq.Bool.Bool.


Require Import Circom.Tuple.
Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import BabyJubjub.
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Crypto.Algebra.Ring Crypto.Algebra.Field.

Require Import Util.
Require Import Circom.Circom Circom.Default.

(* Circuit:
* https://github.com/iden3/circomlib/blob/master/circuits/gates.circom
*)

Local Open Scope list_scope.
Local Open Scope F_scope.

Module Gates (C: CIRCOM).

Import C.

Module XOR.
(* template XOR() {
    signal input a;
    signal input b;
    signal output out;
    out <== a + b - 2*a*b;
} *)

Definition cons (a b out: F) :=
  out = a + b - (1 + 1) * a * b.

Record t := { a:F; b:F; out:F; _cons: cons a b out; }.

Theorem soundness: forall (c: t), 
  (* pre-conditions *)
  binary c.(a) ->
  binary c.(b) ->
  (* post-conditions *)
  if (c.(a) = c.(b))? then c.(out) = 0 else c.(out) = 1 /\
  binary c.(out).
Proof.
  unwrap_C.
  intros c Ha Hb. destruct c as [a b c _cons].
  unfold cons in *. simpl in *.
  destruct Ha; destruct Hb;
  destruct (dec (a=1)); destruct (dec (b=1)); destruct (dec (c=1));
  destruct (dec (a=b));
  try fqsatz; split; try auto;
  try solve[left; fqsatz]; try solve[right; fqsatz].
Qed.
End XOR.



Module AND.
(* template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
} *)

Definition cons (a b out: F) :=
  out = a * b.

Record t := { a:F; b:F; out:F; _cons: cons a b out; }.

Theorem soundness: forall (c: t), 
  (* pre-conditions *)
  binary c.(a) ->
  binary c.(b) ->
  (* post-conditions *)
  binary c.(out) /\
  ((c.(a) = 1)?) && ((c.(b) = 1)?) = ((c.(out) = 1)?).
Proof.
  unwrap_C.
  intros c Ha Hb. destruct c as [a b c _cons].
  unfold cons in *. simpl in *.
  destruct Ha; destruct Hb;
  destruct (dec (a=1)); destruct (dec (b=1)); destruct (dec (c=1));
  try fqsatz; split; try auto; 
  try solve[left; fqsatz]; try solve[right; fqsatz].
Qed.

Lemma is_sound (c: t):
  binary c.(a) ->
  binary c.(b) ->
  (c.(out) = 1 <-> (c.(a) = 1 /\ c.(b) = 1)).
Proof.
  unwrap_C.
  intros Hbin_a Hbin_b.
  specialize (soundness c).
  destruct Hbin_a; destruct Hbin_b;
  destruct (dec (a c = 1)); 
  destruct (dec (b c = 1)); 
  destruct (dec (out c = 1)); intuition;
  try (rewrite H in *; fqsatz);
  unfold binary in *; simpl in *;
  try (exfalso; destruct H1; auto; discriminate).
Qed.


Lemma is_binary (c: t):
  binary c.(a) ->
  binary c.(b) ->
  binary c.(out).
Proof. specialize (soundness c). intuition. Qed.

Definition wgen: t. Admitted.

#[global] Instance Default: Default t. constructor. exact wgen. Defined.

End AND.



Module OR.
(* template OR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - a*b;
} *)
Definition cons (a b out: F) :=
  out = a + b - a*b.

Record t := { a:F; b:F; out:F; _cons: cons a b out; }.

Theorem soundness: forall (c: t), 
  (* pre-conditions *)
  binary c.(a) ->
  binary c.(b) ->
  (* post-conditions *)
  binary c.(out) /\
  ((c.(a) = 1)?) || ((c.(b) = 1)?) = ((c.(out) = 1)?).
Proof.
  unwrap_C.
  intros c Ha Hb. destruct c as [a b c _cons].
  unfold cons in *. simpl in *.
  destruct Ha; destruct Hb;
  destruct (dec (a=1)); destruct (dec (b=1)); destruct (dec (c=1));
  try fqsatz; split; try auto; 
  try solve[left; fqsatz]; try solve[right; fqsatz].
Qed.

Lemma is_sound (c: t):
  binary c.(a) ->
  binary c.(b) ->
  (c.(out) = 1 <-> (c.(a) = 1 \/ c.(b) = 1)).
Proof.
  unwrap_C.
  intros Hbin_a Hbin_b.
  specialize (soundness c).
  destruct Hbin_a; destruct Hbin_b;
  destruct (dec (a c = 1)); 
  destruct (dec (b c = 1)); 
  destruct (dec (out c = 1)); intuition;
  try (rewrite H in *; fqsatz);
  unfold binary in *; simpl in *;
  try (exfalso; destruct H1; auto; discriminate).
Qed.


Lemma is_binary (c: t):
  binary c.(a) ->
  binary c.(b) ->
  binary c.(out).
Proof. specialize (soundness c). intuition. Qed.

Definition wgen: t. Admitted.

#[global] Instance Default: Default t. constructor. exact wgen. Defined.
End OR.


Module TODO.
(* 
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
Qed. *)

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

End TODO.

End Gates.