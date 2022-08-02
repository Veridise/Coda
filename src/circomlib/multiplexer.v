Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.Znumtheory.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.


Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Decidable Crypto.Util.Notations.
Require Import BabyJubjub.
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Crypto.Algebra.Ring Crypto.Algebra.Field.

Require Import Circom.Circom Circom.DSL.

(* Circuit:
* https://github.com/iden3/circomlib/blob/master/circuits/multiplexer.circom
*)

Local Open Scope list_scope.
Local Open Scope F_scope.

Module Multiplexer (C: CIRCOM).
Module D := DSL C.
Import C D.

Local Open Scope list_scope.
Local Open Scope F_scope.

Local Notation "a [ b ]" := (Tuple.nth_default 0 b a).

(* template EscalarProduct(w) {
    signal input in1[w];
    signal input in2[w];
    signal output out;
    signal aux[w];
    var lc = 0;
    for (var i=0; i<w; i++) {
        aux[i] <== in1[i]*in2[i];
        lc = lc + aux[i];
    }
    out <== lc;
} *)

Definition EscalarProduct w (in1 in2: tuple F w) out : Prop :=
  exists (aux: tuple F w),
  let lc := 0 in
  let '(lc, _C) := (iter (fun i '(lc, _C) =>
      (lc + aux[i],
      (aux[i] = in1[i] * in2[i]) /\ _C))
    w
    (lc, True)) in
  (lc = out) /\ _C.

Definition EscalarProductSpec n w (in1 in2 : tuple F w) out :=
  out = fold_right (fun a b : F => a + b) 0
         (firstn n (to_list w (map2 (fun a b : F => a * b) in1 in2))).

Theorem EscalarProductSoundness:
  forall w in1 in2 out,
  EscalarProduct w in1 in2 out -> EscalarProductSpec w w in1 in2 out.
Proof.
  unfold EscalarProduct. unfold EscalarProductSpec.
  (* iter initialization *)
  remember (0, True) as a0.
  intros. destruct H as [aux].
  (* iter Invariant *)
  pose (Inv := fun i '((lc1, _C): (F.F q * Prop)) =>
       (_C -> EscalarProductSpec i w in1 in2 out)).
  (* iter function *)
  match goal with
  | [ H: context[match ?it ?f ?n ?init with _ => _ end] |- _ ] =>
    let x := fresh "f" in remember f as x
  end.
  (* invariant holds *)
  assert (Hinv: forall i, Inv i (iter f i a0)). {
  intros. apply iter_inv; unfold Inv.
  - (* base case *) 
    subst. intros. unfold EscalarProductSpec in *. admit.
  - (* inductive case *)
    intros j res Hprev.
    destruct res.
    rewrite Heqf.
    intros.
    destruct H1 as [Hstep HP].
    specialize  (Hprev HP).
    assert (H_j0_leq: (j < S j)%nat) by lia.
    admit.
   }
  unfold Inv in Hinv.
  specialize (Hinv O).
  destruct (iter f O a0).
  intuition.
Abort.


(* template Decoder(w) {
    signal input inp;
    signal output out[w];
    signal output success;
    var lc=0;

    for (var i=0; i<w; i++) {
        out[i] <-- (inp == i) ? 1 : 0;
        out[i] * (inp-i) === 0;
        lc = lc + out[i];
    }

    lc ==> success;
    success * (success -1) === 0;
} *)

Definition ite {T:Type}{T1:Prop} (e: Decidable T1) (a b: T) := if e then a else b.

Definition Decoder w inp (out: tuple F w) success : Prop :=
  let lc := 0 in
  let '(lc, _C) := (iter (fun i '(lc, _C) =>
      (lc + out[i],
        (out[i] = ite (F.eq_dec inp (F.of_nat q i)) 1 0) /\
        (out[i] * (inp - (F.of_nat q i)) = 0) /\ _C))
    w
    (lc, True)) in
  (lc = success) /\ (success * (success -1) = 0) /\ _C.

Definition get_n_m {wIn nIn}(t: tuple (tuple F wIn) (S nIn)) p m := 
  let ins := (nth_default (hd t) p t) in
  nth_default 0 m ins.

(* template Multiplexer(wIn, nIn) {
    signal input inp[nIn][wIn];
    signal input sel;
    signal output out[wIn];
    component dec = Decoder(nIn);
    component ep[wIn];

    for (var k=0; k<wIn; k++) {
        ep[k] = EscalarProduct(nIn);
    }

    sel ==> dec.inp;
    for (var j=0; j<wIn; j++) {
        for (var k=0; k<nIn; k++) {
            inp[k][j] ==> ep[j].in1[k];
            dec.out[k] ==> ep[j].in2[k];
        }
        ep[j].out ==> out[j];
    }
    dec.success === 1;
} *)

(* require: nIn > 0 *)
Definition Multiplexer 
  wIn nIn sel (inp: tuple (tuple F wIn) (S (nIn - 1))) 
  (out: tuple F wIn) : Prop :=
exists (ep_in1 ep_in2: tuple (tuple F nIn) (S (wIn - 1))) (ep_out: tuple F nIn) dec_out,
  let '_C2 := (iter  (fun j '_C =>
      (let '_C3 := (iter (fun k '_C =>
          (get_n_m inp k j = get_n_m ep_in1 j k /\ 
           dec_out[k] = get_n_m ep_in2 j k /\ _C))
           nIn True) in
              ep_out[j] = out[j] /\
              EscalarProduct nIn (nth_default (hd ep_in1) j ep_in1) (nth_default (hd ep_in2) j ep_in2) (ep_out[j]) /\ _C3
        ))
    wIn True) in
  (Decoder nIn sel dec_out 1) /\ _C2.

End Multiplexer.