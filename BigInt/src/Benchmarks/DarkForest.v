(** * DSL benchmark: Dark Forest *)

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
Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.

From Circom Require Import Circom DSL Util Default Tuple ListUtil LibTactics Signed Simplify Repr Coda.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Definition MiMCSponge (nInputs nRounds nOutputs : nat) (ins : list F) (KEY : F) : list F :=
  List.repeat 0%F nOutputs.

Local Notation "4" := (1 + 1 + 1 + 1)%F.
Local Notation "8" := (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)%F.

(** ** CalculateTotal *)

(* print_endline (generate_lemmas calc_total (typecheck_circuit d_empty calc_total));; *)

Lemma CalculateTotal_obligation0_trivial: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x9 => True) _in -> ((length _in) = n) -> True -> ((v = 0%nat) -> True).
Proof. intuit. Qed.

Lemma CalculateTotal_obligation1_trivial: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x10 => True) _in -> ((length _in) = n) -> True -> (((v = n) /\ True) -> True).
Proof. intuit. Qed.

Lemma CalculateTotal_obligation2_trivial: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x11 => True) _in -> ((length _in) = n) -> True -> (((0%nat <= v) /\ (v < n)) -> True).
Proof. intuit. Qed.

Lemma CalculateTotal_obligation3_trivial: forall (n : nat) (_in : (list F)) (i : nat) (v : F), Forall (fun x12 => True) _in -> ((length _in) = n) -> (i < n) -> True -> ((v = (sum (take i _in))) -> True).
Proof. intuit. Qed.

Lemma CalculateTotal_obligation4_trivial: forall (n : nat) (_in : (list F)) (i : nat) (x : F) (v : F), Forall (fun x13 => True) _in -> ((length _in) = n) -> (i < n) -> (x = (sum (take i _in))) -> True -> (((v = x) /\ True) -> True).
Proof. intuit. Qed.

Lemma CalculateTotal_obligation5_trivial: forall (n : nat) (_in : (list F)) (i : nat) (x : F) (v : F), Forall (fun x14 => True) _in -> ((length _in) = n) -> (i < n) -> (x = (sum (take i _in))) -> True -> ((v = (_in!i)) -> True).
Proof. intuit. Qed.

Lemma CalculateTotal_obligation6: forall (n : nat) (_in : (list F)) (i : nat) (x : F) (v : F), Forall (fun x15 => True) _in -> ((length _in) = n) -> (i < n) -> (x = (sum (take i _in))) -> True -> ((v = (x + (_in!i))%F) -> (v = (sum (take (i + 1%nat)%nat _in)))).
Proof.
  unfold take; intros; subst.
  apply sum_step; auto.
Qed.

Lemma CalculateTotal_obligation7: forall (n : nat) (_in : (list F)) (v : F), Forall (fun x16 => True) _in -> ((length _in) = n) -> True -> ((v = 0%F) -> (v = (sum (take 0%nat _in)))).
Proof. auto. Qed.

Lemma CalculateTotal_obligation8: forall (n : nat) (_in : (list F)) (v : F), Forall (fun x17 => True) _in -> ((length _in) = n) -> True -> ((v = (sum (take n _in))) -> (v = (sum _in))).
Proof.
  unfold take; intros; subst.
  rewrite firstn_all; auto.
Qed.

(** ** QuinSelector *)

(* print_endline (generate_lemmas quin_selector (typecheck_circuit (add_to_deltas d_empty [is_equal; less_than; calc_total]) quin_selector));; *)

Lemma QuinSelector_obligation0: forall (choices : F) (_in : (list F)) (index : F) (v : Z), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x0 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> True -> ((v = 4%nat) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof.
  intuit; subst; lia.
Qed.

Lemma QuinSelector_obligation1: forall (choices : F) (_in : (list F)) (index : F) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x1 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> True -> (((v = index) /\ True) -> ((^ v) < (2%nat ^ 4%nat)%Z)).
Proof.
  intuit; subst; lia.
Qed.

Lemma QuinSelector_obligation2: forall (choices : F) (_in : (list F)) (index : F) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x2 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> True -> (((v = choices) /\ True) -> ((^ v) < (2%nat ^ 4%nat)%Z)).
Proof.
  intuit; subst; lia.
Qed.

Lemma QuinSelector_obligation3_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (v : Z), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x3 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> True -> ((v = 0%nat) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation4_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x4 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> True -> (((v = choices) /\ True) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation5_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (v : Z), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x5 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> True -> ((v = (^ choices)) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation6_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (v : Z), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x6 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> True -> (((0%nat <= v) /\ (v < (^ choices))) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation7_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (i : nat) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x7 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> (i < (^ choices)) -> True -> (((^ v) = i) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation8_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (i : nat) (v : (list F)), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x8 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> (i < (^ choices)) -> Forall (fun x9 => True) v -> True -> (((forall (jg:nat), 0%nat <= jg < i -> ((^ (v!jg)) = jg)) /\ ((length v) = i)) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation9_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (i : nat) (f_x : (F * (list F))) (f : F) (x : (list F)) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x10 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> (i < (^ choices)) -> match f_x with (x12,x13) => ((^ x12) = i) end -> match f_x with (x12,x13) => Forall (fun x11 => True) x13 end -> match f_x with (x12,x13) => ((forall (jg:nat), 0%nat <= jg < i -> ((^ (x13!jg)) = jg)) /\ ((length x13) = i)) end -> match f_x with (x12,x13) => True end -> True -> Forall (fun x14 => True) x -> True -> True -> (((v = f) /\ True) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation10_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (i : nat) (f_x : (F * (list F))) (f : F) (x : (list F)) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x15 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> (i < (^ choices)) -> match f_x with (x17,x18) => ((^ x17) = i) end -> match f_x with (x17,x18) => Forall (fun x16 => True) x18 end -> match f_x with (x17,x18) => ((forall (jg:nat), 0%nat <= jg < i -> ((^ (x18!jg)) = jg)) /\ ((length x18) = i)) end -> match f_x with (x17,x18) => True end -> True -> Forall (fun x19 => True) x -> True -> True -> ((v = 1%F) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation11: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (i : nat) (f_x : (F * (list F))) (f : F) (x : (list F)) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x20 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> (i < (^ choices)) -> match f_x with (x22,x23) => ((^ x22) = i) end -> match f_x with (x22,x23) => Forall (fun x21 => True) x23 end -> match f_x with (x22,x23) => ((forall (jg:nat), 0%nat <= jg < i -> ((^ (x23!jg)) = jg)) /\ ((length x23) = i)) end -> match f_x with (x22,x23) => True end -> True -> Forall (fun x24 => True) x -> True -> True -> ((v = (f + 1%F)%F) -> ((^ v) = (i + 1%nat)%nat)).
Proof. Admitted.

Lemma QuinSelector_obligation12: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (i : nat) (f_x : (F * (list F))) (f : F) (x : (list F)) (v : (list F)), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x25 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> (i < (^ choices)) -> match f_x with (x27,x28) => ((^ x27) = i) end -> match f_x with (x27,x28) => Forall (fun x26 => True) x28 end -> match f_x with (x27,x28) => ((forall (jg:nat), 0%nat <= jg < i -> ((^ (x28!jg)) = jg)) /\ ((length x28) = i)) end -> match f_x with (x27,x28) => True end -> True -> Forall (fun x29 => True) x -> True -> Forall (fun x30 => True) v -> True -> (((v = (x ++ (f :: nil))) /\ ((length v) = ((length x) + (length (f :: nil)))%nat)) -> ((forall (jg:nat), 0%nat <= jg < (i + 1%nat)%nat -> ((^ (v!jg)) = jg)) /\ ((length v) = (i + 1%nat)%nat))).
Proof. Admitted.

Lemma QuinSelector_obligation13_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (i : nat) (f_x : (F * (list F))) (f : F) (x : (list F)) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x31 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> (i < (^ choices)) -> match f_x with (x33,x34) => ((^ x33) = i) end -> match f_x with (x33,x34) => Forall (fun x32 => True) x34 end -> match f_x with (x33,x34) => ((forall (jg:nat), 0%nat <= jg < i -> ((^ (x34!jg)) = jg)) /\ ((length x34) = i)) end -> match f_x with (x33,x34) => True end -> True -> Forall (fun x35 => True) x -> True -> True -> (True -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation14_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (i : nat) (f_x : (F * (list F))) (f : F) (x : (list F)), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x36 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> (i < (^ choices)) -> match f_x with (x38,x39) => ((^ x38) = i) end -> match f_x with (x38,x39) => Forall (fun x37 => True) x39 end -> match f_x with (x38,x39) => ((forall (jg:nat), 0%nat <= jg < i -> ((^ (x39!jg)) = jg)) /\ ((length x39) = i)) end -> match f_x with (x38,x39) => True end -> True -> Forall (fun x40 => True) x -> True -> (True -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation15: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x41 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> True -> ((v = 0%F) -> ((^ v) = 0%nat)).
Proof.
  intuit; subst; simpl.
  rewrite Zmod_0_l.
  reflexivity.
Qed.

Lemma QuinSelector_obligation16: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (v : (list F)), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x42 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> Forall (fun x43 => True) v -> True -> ((v = nil) -> ((forall (jg:nat), 0%nat <= jg < 0%nat -> ((^ (v!jg)) = jg)) /\ ((length v) = 0%nat))).
Proof.
  intuit; subst; simpl in *; lia.
Qed.

Lemma QuinSelector_obligation17_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x44 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> True -> (True -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation18_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x45 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> (True -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation19_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (__rng : (F * (list F))) (_ : F) (rng : (list F)) (x : F) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x46 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> match __rng with (x48,x49) => ((^ x48) = (^ choices)) end -> match __rng with (x48,x49) => Forall (fun x47 => True) x49 end -> match __rng with (x48,x49) => ((forall (jg:nat), 0%nat <= jg < (^ choices) -> ((^ (x49!jg)) = jg)) /\ (Z.of_nat (length x49) = (^ choices))) end -> match __rng with (x48,x49) => True end -> True -> Forall (fun x50 => True) rng -> True -> True -> True -> (((v = x) /\ True) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation20_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (__rng : (F * (list F))) (_ : F) (rng : (list F)) (x : F) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x51 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> match __rng with (x53,x54) => ((^ x53) = (^ choices)) end -> match __rng with (x53,x54) => Forall (fun x52 => True) x54 end -> match __rng with (x53,x54) => ((forall (jg:nat), 0%nat <= jg < (^ choices) -> ((^ (x54!jg)) = jg)) /\ (Z.of_nat (length x54) = (^ choices))) end -> match __rng with (x53,x54) => True end -> True -> Forall (fun x55 => True) rng -> True -> True -> True -> (((v = index) /\ True) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation21_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (__rng : (F * (list F))) (_ : F) (rng : (list F)) (eqs : (list F)) (xy_s : (list (F * F))) (xmy_s : (list F)) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x56 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> match __rng with (x58,x59) => ((^ x58) = (^ choices)) end -> match __rng with (x58,x59) => Forall (fun x57 => True) x59 end -> match __rng with (x58,x59) => ((forall (jg:nat), 0%nat <= jg < (^ choices) -> ((^ (x59!jg)) = jg)) /\ (Z.of_nat (length x59) = (^ choices))) end -> match __rng with (x58,x59) => True end -> True -> Forall (fun x60 => True) rng -> True -> Forall (fun x61 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length rng) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((rng!im) = index)) /\ (((eqs!im) = 0%F) -> ~((rng!im) = index))))) /\ ((length eqs) = (length rng))) -> Forall (fun x64 => match x64 with (x62,x63) => True end) xy_s -> Forall (fun x64 => match x64 with (x62,x63) => True end) xy_s -> Forall (fun x64 => match x64 with (x62,x63) => True end) xy_s -> ((forall (iz:nat), 0%nat <= iz < (length _in) -> (((fst (xy_s!iz)) = (_in!iz)) /\ ((snd (xy_s!iz)) = (eqs!iz)))) /\ ((length xy_s) = (length _in))) -> Forall (fun x65 => True) xmy_s -> ((forall (im:nat), 0%nat <= im < (length xy_s) -> ((xmy_s!im) = ((fst (xy_s!im)) * (snd (xy_s!im)))%F)) /\ ((length xmy_s) = (length xy_s))) -> True -> (((v = choices) /\ True) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation22: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (__rng : (F * (list F))) (_ : F) (rng : (list F)) (eqs : (list F)) (xy_s : (list (F * F))) (xmy_s : (list F)) (v : Z), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x66 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> match __rng with (x68,x69) => ((^ x68) = (^ choices)) end -> match __rng with (x68,x69) => Forall (fun x67 => True) x69 end -> match __rng with (x68,x69) => ((forall (jg:nat), 0%nat <= jg < (^ choices) -> ((^ (x69!jg)) = jg)) /\ (Z.of_nat (length x69) = (^ choices))) end -> match __rng with (x68,x69) => True end -> True -> Forall (fun x70 => True) rng -> True -> Forall (fun x71 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length rng) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((rng!im) = index)) /\ (((eqs!im) = 0%F) -> ~((rng!im) = index))))) /\ ((length eqs) = (length rng))) -> Forall (fun x74 => match x74 with (x72,x73) => True end) xy_s -> Forall (fun x74 => match x74 with (x72,x73) => True end) xy_s -> Forall (fun x74 => match x74 with (x72,x73) => True end) xy_s -> ((forall (iz:nat), 0%nat <= iz < (length _in) -> (((fst (xy_s!iz)) = (_in!iz)) /\ ((snd (xy_s!iz)) = (eqs!iz)))) /\ ((length xy_s) = (length _in))) -> Forall (fun x75 => True) xmy_s -> ((forall (im:nat), 0%nat <= im < (length xy_s) -> ((xmy_s!im) = ((fst (xy_s!im)) * (snd (xy_s!im)))%F)) /\ ((length xmy_s) = (length xy_s))) -> True -> ((v = (^ choices)) -> (0%nat <= v)).
Proof.
  intuit; subst; simpl; lia.
Qed.

Lemma QuinSelector_obligation23: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (__rng : (F * (list F))) (_ : F) (rng : (list F)) (eqs : (list F)) (xy_s : (list (F * F))) (xmy_s : (list F)) (v : (list F)), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x76 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> match __rng with (x78,x79) => ((^ x78) = (^ choices)) end -> match __rng with (x78,x79) => Forall (fun x77 => True) x79 end -> match __rng with (x78,x79) => ((forall (jg:nat), 0%nat <= jg < (^ choices) -> ((^ (x79!jg)) = jg)) /\ (Z.of_nat (length x79) = (^ choices))) end -> match __rng with (x78,x79) => True end -> True -> Forall (fun x80 => True) rng -> True -> Forall (fun x81 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length rng) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((rng!im) = index)) /\ (((eqs!im) = 0%F) -> ~((rng!im) = index))))) /\ ((length eqs) = (length rng))) -> Forall (fun x84 => match x84 with (x82,x83) => True end) xy_s -> Forall (fun x84 => match x84 with (x82,x83) => True end) xy_s -> Forall (fun x84 => match x84 with (x82,x83) => True end) xy_s -> ((forall (iz:nat), 0%nat <= iz < (length _in) -> (((fst (xy_s!iz)) = (_in!iz)) /\ ((snd (xy_s!iz)) = (eqs!iz)))) /\ ((length xy_s) = (length _in))) -> Forall (fun x85 => True) xmy_s -> ((forall (im:nat), 0%nat <= im < (length xy_s) -> ((xmy_s!im) = ((fst (xy_s!im)) * (snd (xy_s!im)))%F)) /\ ((length xmy_s) = (length xy_s))) -> Forall (fun x86 => True) v -> True -> (((v = xmy_s) /\ True) -> (Z.of_nat (length v) = (^ choices))).
Proof.
  intuit; subst; simpl; lia.
Qed.

Lemma QuinSelector_obligation24: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (__rng : (F * (list F))) (_ : F) (rng : (list F)) (eqs : (list F)) (xy_s : (list (F * F))) (xmy_s : (list F)) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x87 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> match __rng with (x89,x90) => ((^ x89) = (^ choices)) end -> match __rng with (x89,x90) => Forall (fun x88 => True) x90 end -> match __rng with (x89,x90) => ((forall (jg:nat), 0%nat <= jg < (^ choices) -> ((^ (x90!jg)) = jg)) /\ (Z.of_nat (length x90) = (^ choices))) end -> match __rng with (x89,x90) => True end -> True -> Forall (fun x91 => True) rng -> True -> Forall (fun x92 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length rng) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((rng!im) = index)) /\ (((eqs!im) = 0%F) -> ~((rng!im) = index))))) /\ ((length eqs) = (length rng))) -> Forall (fun x95 => match x95 with (x93,x94) => True end) xy_s -> Forall (fun x95 => match x95 with (x93,x94) => True end) xy_s -> Forall (fun x95 => match x95 with (x93,x94) => True end) xy_s -> ((forall (iz:nat), 0%nat <= iz < (length _in) -> (((fst (xy_s!iz)) = (_in!iz)) /\ ((snd (xy_s!iz)) = (eqs!iz)))) /\ ((length xy_s) = (length _in))) -> Forall (fun x96 => True) xmy_s -> ((forall (im:nat), 0%nat <= im < (length xy_s) -> ((xmy_s!im) = ((fst (xy_s!im)) * (snd (xy_s!im)))%F)) /\ ((length xmy_s) = (length xy_s))) -> True -> ((v = (sum xmy_s)) -> (((^ index) < (^ choices)) -> (v = (_in!(Z.to_nat (^ index)))))).
Proof. Admitted.

(** IsNegative *)

(* print_endline (generate_lemmas is_neg (typecheck_circuit (add_to_deltas d_empty [num2bits; c_sign]) is_neg));; *)

Lemma IsNegative_obligation0: forall (_in : F) (v : Z), True -> True -> ((v = 254%nat) -> (0%nat <= v)).
Proof. lia. Qed.

Lemma IsNegative_obligation1_trivial: forall (_in : F) (v : F), True -> True -> (((v = _in) /\ True) -> True).
Proof. intuit. Qed.

Lemma IsNegative_obligation2: forall (_in : F) (z : (list F)) (v : (list F)), True -> Forall (fun x0 => ((x0 = 0%F) \/ (x0 = 1%F))) z -> (((as_le_f z) = _in) /\ ((length z) = 254%nat)) -> Forall (fun x1 => True) v -> True -> (((v = z) /\ True) -> ((length v) = 254%nat)).
Proof.
  intuit; subst; lia.
Qed.

Lemma IsNegative_obligation3: forall (_in : F) (z : (list F)) (v : F), True -> Forall (fun x2 => ((x2 = 0%F) \/ (x2 = 1%F))) z -> (((as_le_f z) = _in) /\ ((length z) = 254%nat)) -> True -> (True -> ((v = 0%F) \/ (v = 1%F))).
Proof. Admitted.

Lemma IsNegative_obligation4: forall (_in : F) (z : (list F)) (v : F), True -> Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) z -> (((as_le_f z) = _in) /\ ((length z) = 254%nat)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((Signed.to_Z (as_le_f z)) < 0%nat)) /\ ((v = 0%F) -> ~((Signed.to_Z (as_le_f z)) < 0%nat)))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((Signed.to_Z _in) < 0%nat)) /\ ((v = 0%F) -> ~((Signed.to_Z _in) < 0%nat))))).
Proof.
  intuit; subst; auto.
Qed.

(** ** Random *)

(* print_endline (generate_lemmas random (typecheck_circuit (add_to_deltas d_empty [num2bits; mimc_sponge]) random));; *)

Lemma Random_obligation0: forall (_in : (list F)) (KEY : F) (v : Z), Forall (fun x0 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> True -> ((v = 3%nat) -> (0%nat <= v)).
Proof. lia. Qed.

Lemma Random_obligation1: forall (_in : (list F)) (KEY : F) (v : Z), Forall (fun x1 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> True -> ((v = 4%nat) -> (0%nat <= v)).
Proof. lia. Qed.

Lemma Random_obligation2: forall (_in : (list F)) (KEY : F) (v : Z), Forall (fun x2 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> True -> ((v = 1%nat) -> (0%nat <= v)).
Proof. lia. Qed.

Lemma Random_obligation3: forall (_in : (list F)) (KEY : F) (v : (list F)), Forall (fun x3 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x4 => True) v -> True -> ((((forall (i:nat), 0%nat <= i < (length v) -> ((15%nat < C.q) /\ ((^ (v!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length v) = 3%nat)) /\ (v = _in)) -> ((length v) = 3%nat)).
Proof.
  intuit; subst; auto.
Qed.

Lemma Random_obligation4_trivial: forall (_in : (list F)) (KEY : F) (v : F), Forall (fun x5 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> True -> ((((15%nat < C.q) /\ ((^ v) < (2%nat ^ 32%nat)%Z)) /\ (v = KEY)) -> True).
Proof. intuit. Qed.

Lemma Random_obligation5: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (v : Z), Forall (fun x6 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x7 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> True -> ((v = 254%nat) -> (0%nat <= v)).
Proof. lia. Qed.

Lemma Random_obligation6_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (v : F), Forall (fun x8 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x9 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> True -> (((v = (mimc!0%nat)) /\ (v = z)) -> True).
Proof. intuit. Qed.

Lemma Random_obligation7_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x10 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x11 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x12 => ((x12 = 0%F) \/ (x12 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> ((v = 8%F) -> True).
Proof. intuit. Qed.

Lemma Random_obligation8_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x13 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x14 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x15 => ((x15 = 0%F) \/ (x15 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> (((v = (n2b!3%nat)) /\ (v = n2b3)) -> True).
Proof. intuit. Qed.

Lemma Random_obligation9_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x16 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x17 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x18 => ((x18 = 0%F) \/ (x18 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> ((v = (8%F * n2b3)%F) -> True).
Proof. intuit. Qed.

Lemma Random_obligation10_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x19 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x20 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x21 => ((x21 = 0%F) \/ (x21 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> ((v = 4%F) -> True).
Proof. intuit. Qed.

Lemma Random_obligation11_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x22 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x23 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x24 => ((x24 = 0%F) \/ (x24 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> (((v = (n2b!2%nat)) /\ (v = n2b2)) -> True).
Proof. intuit. Qed.

Lemma Random_obligation12_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x25 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x26 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x27 => ((x27 = 0%F) \/ (x27 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> ((v = (4%F * n2b2)%F) -> True).
Proof. intuit. Qed.

Lemma Random_obligation13_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x28 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x29 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x30 => ((x30 = 0%F) \/ (x30 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> ((v = 2%F) -> True).
Proof. intuit. Qed.

Lemma Random_obligation14_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x31 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x32 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x33 => ((x33 = 0%F) \/ (x33 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> (((v = (n2b!1%nat)) /\ (v = n2b1)) -> True).
Proof. intuit. Qed.

Lemma Random_obligation15_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x34 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x35 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x36 => ((x36 = 0%F) \/ (x36 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> ((v = (2%F * n2b1)%F) -> True).
Proof. intuit. Qed.

Lemma Random_obligation16_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x37 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x38 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x39 => ((x39 = 0%F) \/ (x39 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> (((v = (n2b!0%nat)) /\ (v = n2b0)) -> True).
Proof. intuit. Qed.

Lemma Random_obligation17_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x40 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x41 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x42 => ((x42 = 0%F) \/ (x42 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> ((v = ((2%F * n2b1)%F + n2b0)%F) -> True).
Proof. intuit. Qed.

Lemma Random_obligation18_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x43 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x44 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x45 => ((x45 = 0%F) \/ (x45 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> ((v = ((4%F * n2b2)%F + ((2%F * n2b1)%F + n2b0)%F)%F) -> True).
Proof. intuit. Qed.

Lemma Random_obligation19: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x46 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x47 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x48 => ((x48 = 0%F) \/ (x48 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> ((v = ((8%F * n2b3)%F + ((4%F * n2b2)%F + ((2%F * n2b1)%F + n2b0)%F)%F)%F) -> ((0%nat <= (^ v)) /\ ((^ v) <= 15%nat))).
Proof.
  unwrap_C; intros; subst.
  destruct H1, H6.
  assert (
      H' : forall (i : nat), i < 4 -> n2b ! i = 0%F \/ n2b ! i = 1%F
    ). {
    intros. pattern (n2b ! i).
    assert (i < length n2b) by lia.
    clear H8; revert H9; revert i.
    rewrite <- Forall_nth_default; auto.
  }
  assert (n2b ! 0 = 0%F \/ n2b ! 0 = 1%F) by (apply H'; lia).
  assert (n2b ! 1 = 0%F \/ n2b ! 1 = 1%F) by (apply H'; lia).
  assert (n2b ! 2 = 0%F \/ n2b ! 2 = 1%F) by (apply H'; lia).
  assert (n2b ! 3 = 0%F \/ n2b ! 3 = 1%F) by (apply H'; lia).
  destruct H8, H9, H10, H12;
    rewrite H8, H9, H10, H12;
    try (repeat rewrite Fmul_0_r);
    try (repeat rewrite Fmul_1_r);
    try (repeat rewrite Fadd_0_r);
    try (repeat rewrite Fadd_0_l);
    split; Signed.solve_to_Z.
Qed.
