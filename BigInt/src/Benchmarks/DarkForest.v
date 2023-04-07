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

From Circom Require Import Circom DSL Util Default Tuple ListUtil LibTactics Simplify Repr.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Definition sum := DSLL.sumL_F.
Definition take {A} i (xs : list A) := xs[:i].

Lemma sum_step :
  forall (l : list F) (i : nat),
    i < length l ->
    (sum (l [:i]) + l ! i)%F = sum (l [:i + 1]).
Proof.
  unwrap_C.
  induction l; intros;
    try (simpl in H; lia).
  destruct i; simpl; try fqsatz.
  assert (i < length l).
  { simpl in H; lia. }
  simpl_default; auto.
  rewrite <- IHl; auto.
  fqsatz.
Qed.

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

Lemma QuinSelector_obligation0: forall (choices : F) (_in : (list F)) (index : F) (v : Z), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x18 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> True -> ((v = 4%nat) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof. lia. Qed.

Lemma QuinSelector_obligation1: forall (choices : F) (_in : (list F)) (index : F) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x19 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> True -> (((v = index) /\ True) -> ((^ v) < (2%nat ^ 4%nat)%Z)).
Proof.
  intuit; subst; lia.
Qed.

Lemma QuinSelector_obligation2: forall (choices : F) (_in : (list F)) (index : F) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x20 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> True -> (((v = choices) /\ True) -> ((^ v) < (2%nat ^ 4%nat)%Z)).
Proof.
  intuit; subst; lia.
Qed.

Lemma QuinSelector_obligation3_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (v : Z), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x21 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> True -> ((v = 0%nat) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation4_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x22 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> True -> (((v = choices) /\ True) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation5_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (v : Z), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x23 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> True -> ((v = (^ choices)) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation6_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (v : Z), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x24 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> True -> (((0%nat <= v) /\ (v < (^ choices))) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation7_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (i : nat) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x25 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> (i < (^ choices)) -> True -> (((^ v) = i) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation8_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (i : nat) (v : (list F)), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x26 => True) _in -> ((length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> (i < (^ choices)) -> Forall (fun x27 => True) v -> True -> (((forall (jg:nat), 0%nat <= jg < i -> ((v!jg) = (^ jg))) /\ (Z.of_nat (length v) = jg)) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation9_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (i : nat) (f_x : F * (list F)) (f : F) (x : (list F)) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x28 => True) _in -> ((length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> (i < (^ choices)) -> match f_x with (x30,x31) => ((^ x30) = i) end -> match f_x with (x30,x31) => Forall (fun x29 => True) x31 end -> match f_x with (x30,x31) => ((forall (jg:nat), 0%nat <= jg < i -> ((x31!jg) = (^ jg))) /\ ((length x31) = jg)) end -> match f_x with (x30,x31) => True end -> True -> Forall (fun x32 => True) x -> True -> True -> (((v = f) /\ True) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation10_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (i : nat) (f_x : F * (list F)) (f : F) (x : (list F)) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x33 => True) _in -> ((length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> (i < (^ choices)) -> match f_x with (x35,x36) => ((^ x35) = i) end -> match f_x with (x35,x36) => Forall (fun x34 => True) x36 end -> match f_x with (x35,x36) => ((forall (jg:nat), 0%nat <= jg < i -> ((x36!jg) = (^ jg))) /\ ((length x36) = jg)) end -> match f_x with (x35,x36) => True end -> True -> Forall (fun x37 => True) x -> True -> True -> ((v = 1%F) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation11: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (i : nat) (f_x : F * (list F)) (f : F) (x : (list F)) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x38 => True) _in -> ((length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> (i < (^ choices)) -> match f_x with (x40,x41) => ((^ x40) = i) end -> match f_x with (x40,x41) => Forall (fun x39 => True) x41 end -> match f_x with (x40,x41) => ((forall (jg:nat), 0%nat <= jg < i -> ((x41!jg) = (^ jg))) /\ ((length x41) = jg)) end -> match f_x with (x40,x41) => True end -> True -> Forall (fun x42 => True) x -> True -> True -> ((v = (f + 1%F)%F) -> ((^ v) = (i + 1%nat)%nat)).
Proof. Admitted.

Lemma QuinSelector_obligation12: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (i : nat) (f_x : F * (list F)) (f : F) (x : (list F)) (v : (list F)), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x43 => True) _in -> ((length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> (i < (^ choices)) -> match f_x with (x45,x46) => ((^ x45) = i) end -> match f_x with (x45,x46) => Forall (fun x44 => True) x46 end -> match f_x with (x45,x46) => ((forall (jg:nat), 0%nat <= jg < i -> ((x46!jg) = (^ jg))) /\ ((length x46) = jg)) end -> match f_x with (x45,x46) => True end -> True -> Forall (fun x47 => True) x -> True -> Forall (fun x48 => True) v -> True -> (((v = (x ++ (f :: nil))) /\ ((length v) = ((length x) + (length (f :: nil)))%nat)) -> ((forall (jg:nat), 0%nat <= jg < (i + 1%nat)%nat -> ((v!jg) = (^ jg))) /\ ((length v) = jg))).
Proof. Admitted.

Lemma QuinSelector_obligation13_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (i : nat) (f_x : F * (list F)) (f : F) (x : (list F)) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x49 => True) _in -> ((length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> (i < (^ choices)) -> match f_x with (x51,x52) => ((^ x51) = i) end -> match f_x with (x51,x52) => Forall (fun x50 => True) x52 end -> match f_x with (x51,x52) => ((forall (jg:nat), 0%nat <= jg < i -> ((x52!jg) = (^ jg))) /\ ((length x52) = jg)) end -> match f_x with (x51,x52) => True end -> True -> Forall (fun x53 => True) x -> True -> True -> (True -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation14_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (i : nat) (f_x : F * (list F)) (f : F) (x : (list F)), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x54 => True) _in -> ((length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> (i < (^ choices)) -> match f_x with (x56,x57) => ((^ x56) = i) end -> match f_x with (x56,x57) => Forall (fun x55 => True) x57 end -> match f_x with (x56,x57) => ((forall (jg:nat), 0%nat <= jg < i -> ((x57!jg) = (^ jg))) /\ ((length x57) = jg)) end -> match f_x with (x56,x57) => True end -> True -> Forall (fun x58 => True) x -> True -> (True -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation15: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x59 => True) _in -> ((length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> True -> ((v = 0%F) -> ((^ v) = 0%nat)).
Proof. Admitted.

Lemma QuinSelector_obligation16: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (v : (list F)), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x60 => True) _in -> ((length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> Forall (fun x61 => True) v -> True -> ((v = nil) -> ((forall (jg:nat), 0%nat <= jg < 0%nat -> ((v!jg) = (^ jg))) /\ ((length v) = jg))).
Proof. Admitted.

Lemma QuinSelector_obligation17_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x62 => True) _in -> ((length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> True -> (True -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation18_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x63 => True) _in -> ((length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> (True -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation19_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (__rng : F * (list F)) (_ : F) (rng : (list F)) (x : F) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x64 => True) _in -> ((length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> match __rng with (x66,x67) => ((^ x66) = (^ choices)) end -> match __rng with (x66,x67) => Forall (fun x65 => True) x67 end -> match __rng with (x66,x67) => ((forall (jg:nat), 0%nat <= jg < (^ choices) -> ((x67!jg) = (^ jg))) /\ ((length x67) = jg)) end -> match __rng with (x66,x67) => True end -> True -> Forall (fun x68 => True) rng -> True -> True -> True -> (((v = x) /\ True) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation20_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (__rng : F * (list F)) (_ : F) (rng : (list F)) (x : F) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x69 => True) _in -> ((length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> match __rng with (x71,x72) => ((^ x71) = (^ choices)) end -> match __rng with (x71,x72) => Forall (fun x70 => True) x72 end -> match __rng with (x71,x72) => ((forall (jg:nat), 0%nat <= jg < (^ choices) -> ((x72!jg) = (^ jg))) /\ ((length x72) = jg)) end -> match __rng with (x71,x72) => True end -> True -> Forall (fun x73 => True) rng -> True -> True -> True -> (((v = index) /\ True) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation21_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (__rng : F * (list F)) (_ : F) (rng : (list F)) (eqs : (list F)) (xy_s : (list F * F)) (xmy_s : (list F)) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x74 => True) _in -> ((length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> match __rng with (x76,x77) => ((^ x76) = (^ choices)) end -> match __rng with (x76,x77) => Forall (fun x75 => True) x77 end -> match __rng with (x76,x77) => ((forall (jg:nat), 0%nat <= jg < (^ choices) -> ((x77!jg) = (^ jg))) /\ ((length x77) = jg)) end -> match __rng with (x76,x77) => True end -> True -> Forall (fun x78 => True) rng -> True -> Forall (fun x79 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length rng) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((rng!im) = index)) /\ (((eqs!im) = 0%F) -> ~((rng!im) = index))))) /\ ((length eqs) = (length rng))) -> Forall (fun x82 => match x82 with (x80,x81) => True end) xy_s -> Forall (fun x82 => match x82 with (x80,x81) => True end) xy_s -> Forall (fun x82 => match x82 with (x80,x81) => True end) xy_s -> ((forall (iz:nat), 0%nat <= iz < (length _in) -> (((fst (xy_s!iz)) = (_in!iz)) /\ ((snd (xy_s!iz)) = (eqs!iz)))) /\ ((length xy_s) = (length _in))) -> Forall (fun x83 => True) xmy_s -> ((forall (im:nat), 0%nat <= im < (length xy_s) -> ((xmy_s!im) = ((fst (xy_s!im)) * (snd (xy_s!im)))%F)) /\ ((length xmy_s) = (length xy_s))) -> True -> (((v = choices) /\ True) -> True).
Proof. intuit. Qed.

Lemma QuinSelector_obligation22: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (__rng : F * (list F)) (_ : F) (rng : (list F)) (eqs : (list F)) (xy_s : (list F * F)) (xmy_s : (list F)) (v : Z), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x84 => True) _in -> ((length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> match __rng with (x86,x87) => ((^ x86) = (^ choices)) end -> match __rng with (x86,x87) => Forall (fun x85 => True) x87 end -> match __rng with (x86,x87) => ((forall (jg:nat), 0%nat <= jg < (^ choices) -> ((x87!jg) = (^ jg))) /\ ((length x87) = jg)) end -> match __rng with (x86,x87) => True end -> True -> Forall (fun x88 => True) rng -> True -> Forall (fun x89 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length rng) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((rng!im) = index)) /\ (((eqs!im) = 0%F) -> ~((rng!im) = index))))) /\ ((length eqs) = (length rng))) -> Forall (fun x92 => match x92 with (x90,x91) => True end) xy_s -> Forall (fun x92 => match x92 with (x90,x91) => True end) xy_s -> Forall (fun x92 => match x92 with (x90,x91) => True end) xy_s -> ((forall (iz:nat), 0%nat <= iz < (length _in) -> (((fst (xy_s!iz)) = (_in!iz)) /\ ((snd (xy_s!iz)) = (eqs!iz)))) /\ ((length xy_s) = (length _in))) -> Forall (fun x93 => True) xmy_s -> ((forall (im:nat), 0%nat <= im < (length xy_s) -> ((xmy_s!im) = ((fst (xy_s!im)) * (snd (xy_s!im)))%F)) /\ ((length xmy_s) = (length xy_s))) -> True -> ((v = (^ choices)) -> (0%nat <= v)).
Proof. Admitted.

Lemma QuinSelector_obligation23: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (__rng : F * (list F)) (_ : F) (rng : (list F)) (eqs : (list F)) (xy_s : (list F * F)) (xmy_s : (list F)) (v : (list F)), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x94 => True) _in -> ((length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> match __rng with (x96,x97) => ((^ x96) = (^ choices)) end -> match __rng with (x96,x97) => Forall (fun x95 => True) x97 end -> match __rng with (x96,x97) => ((forall (jg:nat), 0%nat <= jg < (^ choices) -> ((x97!jg) = (^ jg))) /\ ((length x97) = jg)) end -> match __rng with (x96,x97) => True end -> True -> Forall (fun x98 => True) rng -> True -> Forall (fun x99 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length rng) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((rng!im) = index)) /\ (((eqs!im) = 0%F) -> ~((rng!im) = index))))) /\ ((length eqs) = (length rng))) -> Forall (fun x102 => match x102 with (x100,x101) => True end) xy_s -> Forall (fun x102 => match x102 with (x100,x101) => True end) xy_s -> Forall (fun x102 => match x102 with (x100,x101) => True end) xy_s -> ((forall (iz:nat), 0%nat <= iz < (length _in) -> (((fst (xy_s!iz)) = (_in!iz)) /\ ((snd (xy_s!iz)) = (eqs!iz)))) /\ ((length xy_s) = (length _in))) -> Forall (fun x103 => True) xmy_s -> ((forall (im:nat), 0%nat <= im < (length xy_s) -> ((xmy_s!im) = ((fst (xy_s!im)) * (snd (xy_s!im)))%F)) /\ ((length xmy_s) = (length xy_s))) -> Forall (fun x104 => True) v -> True -> (((v = xmy_s) /\ True) -> ((length v) = (^ choices))).
Proof. Admitted.

Lemma QuinSelector_obligation24: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (__rng : F * (list F)) (_ : F) (rng : (list F)) (eqs : (list F)) (xy_s : (list F * F)) (xmy_s : (list F)) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x105 => True) _in -> ((length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> match __rng with (x107,x108) => ((^ x107) = (^ choices)) end -> match __rng with (x107,x108) => Forall (fun x106 => True) x108 end -> match __rng with (x107,x108) => ((forall (jg:nat), 0%nat <= jg < (^ choices) -> ((x108!jg) = (^ jg))) /\ ((length x108) = jg)) end -> match __rng with (x107,x108) => True end -> True -> Forall (fun x109 => True) rng -> True -> Forall (fun x110 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length rng) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((rng!im) = index)) /\ (((eqs!im) = 0%F) -> ~((rng!im) = index))))) /\ ((length eqs) = (length rng))) -> Forall (fun x113 => match x113 with (x111,x112) => True end) xy_s -> Forall (fun x113 => match x113 with (x111,x112) => True end) xy_s -> Forall (fun x113 => match x113 with (x111,x112) => True end) xy_s -> ((forall (iz:nat), 0%nat <= iz < (length _in) -> (((fst (xy_s!iz)) = (_in!iz)) /\ ((snd (xy_s!iz)) = (eqs!iz)))) /\ ((length xy_s) = (length _in))) -> Forall (fun x114 => True) xmy_s -> ((forall (im:nat), 0%nat <= im < (length xy_s) -> ((xmy_s!im) = ((fst (xy_s!im)) * (snd (xy_s!im)))%F)) /\ ((length xmy_s) = (length xy_s))) -> True -> ((v = (sum xmy_s)) -> ((index < choices) -> (v = (_in!index)))).
Proof. Admitted.

(** IsNegative *)

(* print_endline (generate_lemmas is_neg (typecheck_circuit (add_to_deltas d_empty [num2bits; c_sign]) is_neg));; *)

Lemma IsNegative_obligation0: forall (_in : F) (v : Z), True -> True -> ((v = 254%nat) -> (0%nat <= v)).
Proof. Admitted.

Lemma IsNegative_obligation1_trivial: forall (_in : F) (v : F), True -> True -> (((v = _in) /\ True) -> True).
Proof. intuit. Qed.

Lemma IsNegative_obligation2: forall (_in : F) (z : (list F)) (v : (list F)), True -> Forall (fun x169 => ((x169 = 0%F) \/ (x169 = 1%F))) z -> (((as_le_f z) = _in) /\ ((length z) = 254%nat)) -> Forall (fun x170 => True) v -> True -> (((v = z) /\ True) -> ((length v) = 254%nat)).
Proof. Admitted.

Lemma IsNegative_obligation3: forall (_in : F) (z : (list F)) (v : F), True -> Forall (fun x171 => ((x171 = 0%F) \/ (x171 = 1%F))) z -> (((as_le_f z) = _in) /\ ((length z) = 254%nat)) -> True -> (True -> ((v = 0%F) \/ (v = 1%F))).
Proof. Admitted.

Lemma IsNegative_obligation4_trivial: forall (_in : F) (z : (list F)) (v : F), True -> Forall (fun x172 => ((x172 = 0%F) \/ (x172 = 1%F))) z -> (((as_le_f z) = _in) /\ ((length z) = 254%nat)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((Signed.to_Z (as_le_f z)) < 0%nat)) /\ ((v = 0%F) -> ~((Signed.to_Z (as_le_f z)) < 0%nat)))) -> True).
Proof. intuit. Qed.

(** ** Random *)

(* print_endline (generate_lemmas random (typecheck_circuit (add_to_deltas d_empty [num2bits; mimc_sponge]) random));; *)

Lemma Random_obligation0: forall (_in : (list F)) (KEY : F) (v : Z), Forall (fun x115 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> True -> ((v = 3%nat) -> (0%nat <= v)).
Proof. Admitted.

Lemma Random_obligation1: forall (_in : (list F)) (KEY : F) (v : Z), Forall (fun x116 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> True -> ((v = 4%nat) -> (0%nat <= v)).
Proof. Admitted.

Lemma Random_obligation2: forall (_in : (list F)) (KEY : F) (v : Z), Forall (fun x117 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> True -> ((v = 1%nat) -> (0%nat <= v)).
Proof. Admitted.

Lemma Random_obligation3: forall (_in : (list F)) (KEY : F) (v : (list F)), Forall (fun x118 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> Forall (fun x119 => True) v -> True -> (((v = _in) /\ True) -> ((length v) = 3%nat)).
Proof. Admitted.

Lemma Random_obligation4_trivial: forall (_in : (list F)) (KEY : F) (v : F), Forall (fun x120 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> True -> (((v = KEY) /\ True) -> True).
Proof. intuit. Qed.

Lemma Random_obligation5: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (v : Z), Forall (fun x121 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> Forall (fun x122 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> True -> ((v = 254%nat) -> (0%nat <= v)).
Proof. Admitted.

Lemma Random_obligation6_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (v : F), Forall (fun x123 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> Forall (fun x124 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> True -> (((v = z) /\ True) -> True).
Proof. intuit. Qed.

Lemma Random_obligation7_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x125 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> Forall (fun x126 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x127 => ((x127 = 0%F) \/ (x127 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> ((v = 8%F) -> True).
Proof. intuit. Qed.

Lemma Random_obligation8_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x128 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> Forall (fun x129 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x130 => ((x130 = 0%F) \/ (x130 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> (((v = n2b3) /\ True) -> True).
Proof. intuit. Qed.

Lemma Random_obligation9_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x131 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> Forall (fun x132 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x133 => ((x133 = 0%F) \/ (x133 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> ((v = (8%F * n2b3)%F) -> True).
Proof. intuit. Qed.

Lemma Random_obligation10_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x134 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> Forall (fun x135 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x136 => ((x136 = 0%F) \/ (x136 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> ((v = 4%F) -> True).
Proof. intuit. Qed.

Lemma Random_obligation11_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x137 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> Forall (fun x138 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x139 => ((x139 = 0%F) \/ (x139 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> (((v = n2b2) /\ True) -> True).
Proof. intuit. Qed.

Lemma Random_obligation12_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x140 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> Forall (fun x141 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x142 => ((x142 = 0%F) \/ (x142 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> ((v = (4%F * n2b2)%F) -> True).
Proof. intuit. Qed.

Lemma Random_obligation13_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x143 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> Forall (fun x144 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x145 => ((x145 = 0%F) \/ (x145 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> ((v = 2%F) -> True).
Proof. intuit. Qed.

Lemma Random_obligation14_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x146 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> Forall (fun x147 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x148 => ((x148 = 0%F) \/ (x148 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> (((v = n2b1) /\ True) -> True).
Proof. intuit. Qed.

Lemma Random_obligation15_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x149 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> Forall (fun x150 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x151 => ((x151 = 0%F) \/ (x151 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> ((v = (2%F * n2b1)%F) -> True).
Proof. intuit. Qed.

Lemma Random_obligation16_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x152 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> Forall (fun x153 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x154 => ((x154 = 0%F) \/ (x154 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> (((v = n2b0) /\ True) -> True).
Proof. intuit. Qed.

Lemma Random_obligation17_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x155 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> Forall (fun x156 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x157 => ((x157 = 0%F) \/ (x157 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> ((v = ((2%F * n2b1)%F + n2b0)%F) -> True).
Proof. intuit. Qed.

Lemma Random_obligation18_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x158 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> Forall (fun x159 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x160 => ((x160 = 0%F) \/ (x160 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> ((v = ((4%F * n2b2)%F + ((2%F * n2b1)%F + n2b0)%F)%F) -> True).
Proof. intuit. Qed.

Lemma Random_obligation19: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (n2b3 : F) (n2b2 : F) (n2b1 : F) (n2b0 : F) (v : F), Forall (fun x161 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((^ (_in!i)) < (2%nat ^ 32%nat)%Z)) /\ ((length _in) = 3%nat)) -> ((^ KEY) < (2%nat ^ 32%nat)%Z) -> Forall (fun x162 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x163 => ((x163 = 0%F) \/ (x163 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> (n2b3 = (n2b!3%nat)) -> (n2b2 = (n2b!2%nat)) -> (n2b1 = (n2b!1%nat)) -> (n2b0 = (n2b!0%nat)) -> True -> ((v = ((8%F * n2b3)%F + ((4%F * n2b2)%F + ((2%F * n2b1)%F + n2b0)%F)%F)%F) -> ((0%nat <= (^ v)) /\ ((^ v) <= 15%nat))).
Proof. Admitted.
