Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.Znumtheory.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Coq.Bool.Bool.


Require Import Circom.Tuple.
Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import BabyJubjub.
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Crypto.Algebra.Ring Crypto.Algebra.Field.

From Circom Require Import Circom Default LibTactics Util.
Require Import Circom.Circom Circom.Default.

(* Circuit:
* https://github.com/iden3/circomlib/blob/master/circuits/gates.circom
*)

Local Open Scope list_scope.
Local Open Scope F_scope.

Module Gates.

#[local] Hint Extern 10 (_ = _) => fqsatz : core.
#[local] Hint Extern 10 (binary _) => (left; fqsatz) || (right; fqsatz): core.


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
  destruct Ha; destruct Hb; subst; split_dec; intuit;
  auto.
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
  destruct Ha; destruct Hb; subst; split_dec; intuit;
  auto || (exfalso; auto).
Qed.

Lemma is_sound (c: t):
  binary c.(a) ->
  binary c.(b) ->
  (c.(out) = 1 <-> (c.(a) = 1 /\ c.(b) = 1)).
Proof.
  intros Hbin_a Hbin_b.
  specialize (soundness c Hbin_a Hbin_b). intro.
  split_dec; simpl in *; intuit; auto || discriminate.
Qed.


Lemma is_binary (c: t):
  binary c.(a) ->
  binary c.(b) ->
  binary c.(out).
Proof. specialize (soundness c). intuit. Qed.

Definition wgen: t. skip. Defined.

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
  destruct Ha; destruct Hb; subst; split_dec; intuit;
  auto || (exfalso; auto).
Qed.

Lemma is_sound (c: t):
  binary c.(a) ->
  binary c.(b) ->
  (c.(out) = 1 <-> (c.(a) = 1 \/ c.(b) = 1)).
Proof.
  intros Hbin_a Hbin_b.
  specialize (soundness c Hbin_a Hbin_b). intro.
  split_dec; simpl in *; intuit; auto || discriminate.
Qed.


Lemma is_binary (c: t):
  binary c.(a) ->
  binary c.(b) ->
  binary c.(out).
Proof. specialize (soundness c). intuition idtac. Qed.

Definition wgen: t. skip. Defined.

#[global] Instance Default: Default t. constructor. exact wgen. Defined.
End OR.



Module NOT.
(* template NOT() {
    signal input in;
    signal output out;

    out <== 1 + in - 2*in;
} *)
Definition cons (_in out: F) :=
  out = 1 + _in - (1 + 1) * _in.

Record t := { _in:F; out:F; _cons: cons _in out; }.

Lemma not_0_eq_1: (0:F) <> (1:F).
Proof. unwrap_C. fqsatz.
Qed.

Theorem soundness: forall (c: t), 
  (* pre-conditions *)
  binary c.(_in) ->
  (* post-conditions *)
  binary c.(out) /\
  ((c.(_in) = 1)?) = ((c.(out) = 0)?).
Proof.
  unwrap_C.
  intros c Ha. destruct c as [_in out _cons].
  unfold cons in *. simpl in *.
  destruct Ha; subst; split_dec; intuit; auto || (exfalso; auto).
Qed.

Definition wgen: t. skip. Defined.

#[global] Instance Default: Default t. constructor. exact wgen. Defined.
End NOT.



Module NAND.
(* template NAND() {
    signal input a;
    signal input b;
    signal output out;

    out <== 1 - a*b;
} *)

Definition cons (a b out: F) :=
  out = 1 - a * b.

Record t := { a:F; b:F; out:F; _cons: cons a b out; }.

Theorem soundness: forall (c: t), 
  (* pre-conditions *)
  binary c.(a) ->
  binary c.(b) ->
  (* post-conditions *)
  binary c.(out) /\
  ((c.(a) = 1)?) && ((c.(b) = 1)?) = ((c.(out) = 0)?).
Proof.
  unwrap_C.
  intros c Ha Hb. destruct c as [a b c _cons].
  unfold cons in *. simpl in *.
  destruct Ha; destruct Hb; subst; split_dec; intuit;
  auto || (exfalso; auto).
Qed.

Definition wgen: t. skip. Defined.

#[global] Instance Default: Default t. constructor. exact wgen. Defined.

End NAND.



Module NOR.
(* template NOR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b + 1 - a - b;
} *)
Definition cons (a b out: F) :=
  out = a*b + 1 - a - b.

Record t := { a:F; b:F; out:F; _cons: cons a b out; }.

Theorem soundness: forall (c: t), 
  (* pre-conditions *)
  binary c.(a) ->
  binary c.(b) ->
  (* post-conditions *)
  binary c.(out) /\
  ((c.(a) = 1)?) || ((c.(b) = 1)?) = ((c.(out) = 0)?).
Proof.
  unwrap_C.
  intros c Ha Hb. destruct c as [a b c _cons].
  unfold cons in *. simpl in *.
  destruct Ha; destruct Hb; subst; split_dec; intuit;
  auto || (exfalso; auto).
Qed.

Definition wgen: t. skip. Defined.

#[global] Instance Default: Default t. constructor. exact wgen. Defined.
End NOR.


Module MultiAND.

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

End MultiAND.

End Gates.