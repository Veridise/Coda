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

#[global]Hint Extern 10 (Forall _ (firstn _ _)) => apply Forall_firstn: core.
#[global]Hint Extern 10  => match goal with
   | [ |- context[List_nth_Default _ _] ] => unfold_default end: core.
   #[global]Hint Extern 10  => match goal with
   | [ |- context[List.nth  _ _ _] ] => apply Forall_nth end: core.
#[global]Hint Extern 10 => match goal with
  [ |- context[length _] ] => rewrite_length end: core.
#[global]Hint Extern 10 (Forall _ (skipn _ _)) => apply Forall_skipn: core.

#[global]Hint Extern 10 (Forall _ (_ :: _)) => constructor: core.
#[global]Hint Extern 10 (Z.of_N (N.of_nat _)) => rewrite nat_N_Z: core.
#[global]Hint Extern 10  => repeat match goal with
  [ H: context[Z.of_N (N.of_nat _)] |- _] => rewrite nat_N_Z in H end: core.

#[global]Hint Extern 10 (_ < _) => lia: core.
#[global]Hint Extern 10 (_ < _)%nat => lia: core.
#[global]Hint Extern 10 (_ <= _) => lia: core.
#[global]Hint Extern 10 (_ <= _)%nat => lia: core.
#[global]Hint Extern 10 (_ > _) => lia: core.
#[global]Hint Extern 10 (_ > _)%nat => lia: core.
#[global]Hint Extern 10 (_ >= _) => lia: core.
#[global]Hint Extern 10 (_ >= _)%nat => lia: core.
#[global]Hint Extern 10 (S _ = S _) => f_equal: core.

(** The sum of a [list F] with at most one nonzero element is just
that element *)

Lemma sum_one_hot :
  forall (xs : list F) (i : nat),
    Z.of_N (N.of_nat 0) <= Z.of_N (N.of_nat i) < Z.of_N (N.of_nat (length xs)) ->
    (forall (j : nat),
        Z.of_N (N.of_nat 0) <= Z.of_N (N.of_nat j) < Z.of_N (N.of_nat (length xs))
        /\ j <> i -> xs ! j = 0%F) ->
    sum xs = xs ! i.
Proof.
Admitted.

(** ** CalculateTotal *)

Lemma CalculateTotal_obligation0_trivial: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x0 => True) _in -> ((length _in) = n) -> True -> ((v = 0%nat) -> True).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation1_trivial: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x1 => True) _in -> ((length _in) = n) -> True -> (((0%nat <= v) /\ (v = n)) -> True).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation2_trivial: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x2 => True) _in -> ((length _in) = n) -> True -> (((0%nat <= v) /\ (v < n)) -> True).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation3_trivial: forall (n : nat) (_in : (list F)) (i : nat) (v : F), Forall (fun x3 => True) _in -> ((length _in) = n) -> (i < n) -> True -> ((v = (sum (take i _in))) -> True).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation4_trivial: forall (n : nat) (_in : (list F)) (i : nat) (x : F) (v : F), Forall (fun x4 => True) _in -> ((length _in) = n) -> (i < n) -> (x = (sum (take i _in))) -> True -> (((v = (sum (take i _in))) /\ (v = x)) -> True).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation5_trivial: forall (n : nat) (_in : (list F)) (i : nat) (x : F) (v : F), Forall (fun x5 => True) _in -> ((length _in) = n) -> (i < n) -> (x = (sum (take i _in))) -> True -> ((v = (_in!i)) -> True).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation6: forall (n : nat) (_in : (list F)) (i : nat) (x : F) (v : F), Forall (fun x6 => True) _in -> ((length _in) = n) -> (i < n) -> (x = (sum (take i _in))) -> True -> ((v = (x + (_in!i))%F) -> (v = (sum (take (i + 1%nat)%nat _in)))).
Proof.
  unfold take; intros; subst.
  apply sum_step; auto.
Qed.

Lemma CalculateTotal_obligation7: forall (n : nat) (_in : (list F)) (v : F), Forall (fun x7 => True) _in -> ((length _in) = n) -> True -> ((v = 0%F) -> (v = (sum (take 0%nat _in)))).
Proof. hammer. Qed.

Lemma CalculateTotal_obligation8: forall (n : nat) (_in : (list F)) (v : F), Forall (fun x8 => True) _in -> ((length _in) = n) -> True -> ((v = (sum (take n _in))) -> (v = (sum _in))).
Proof.
  unfold take; intros; subst.
  rewrite firstn_all; auto.
Qed.

(** ** QuinSelector *)

Lemma QuinSelector_obligation0: forall (choices : F) (_in : (list F)) (index : F) (v : Z), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x0 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> True -> ((v = 4%nat) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof. hammer. Qed.

Lemma QuinSelector_obligation1: forall (choices : F) (_in : (list F)) (index : F) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x1 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> True -> ((((^ v) < (^ choices)) /\ (v = index)) -> ((^ v) <= ((2%nat ^ 4%nat)%Z - 1%nat)%Z)).
Proof. hammer. Qed.

Lemma QuinSelector_obligation2: forall (choices : F) (_in : (list F)) (index : F) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x2 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> True -> ((((4%nat < (C.k - 1%nat)%Z) /\ ((^ v) < (2%nat ^ 4%nat)%Z)) /\ (v = choices)) -> ((^ v) <= ((2%nat ^ 4%nat)%Z - 1%nat)%Z)).
Proof. hammer. Qed.

Lemma QuinSelector_obligation3_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x3 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> True -> ((((4%nat < (C.k - 1%nat)%Z) /\ ((^ v) < (2%nat ^ 4%nat)%Z)) /\ (v = choices)) -> True).
Proof. hammer. Qed.

Lemma QuinSelector_obligation4: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (v : Z), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x4 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> True -> ((v = (^ choices)) -> ((0%nat <= v) /\ (v < C.q))).
Proof.
  unwrap_C; intuit; subst; try lia.
  assert (
      Z.of_N (N.of_nat 2) ^ Z.of_N (N.of_nat 4)
      < Z.of_N (N.of_nat 2) ^ (k - Z.of_N (N.of_nat 1))
    ) by (apply Z.pow_lt_mono_r; auto).
  assert (
      2 ^ (k - Z.of_N (N.of_nat 1)) < 2 ^ k
    ) by (apply Z.pow_lt_mono_r; auto).
  lia.
Qed.

Lemma QuinSelector_obligation5_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (rng : (list F)) (x : F) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x5 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> Forall (fun x6 => True) rng -> ((forall (rng_j:nat), 0%nat <= rng_j < (^ choices) -> ((^ (rng!rng_j)) = rng_j)) /\ (Z.of_nat (length rng) = (^ choices))) -> True -> True -> ((v = x) -> True).
Proof. hammer. Qed.

Lemma QuinSelector_obligation6_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (rng : (list F)) (x : F) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x7 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> Forall (fun x8 => True) rng -> ((forall (rng_j:nat), 0%nat <= rng_j < (^ choices) -> ((^ (rng!rng_j)) = rng_j)) /\ (Z.of_nat (length rng) = (^ choices))) -> True -> True -> ((((^ v) < (^ choices)) /\ (v = index)) -> True).
Proof. hammer. Qed.

Lemma QuinSelector_obligation7_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (rng : (list F)) (eqs : (list F)) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x9 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> Forall (fun x10 => True) rng -> ((forall (rng_j:nat), 0%nat <= rng_j < (^ choices) -> ((^ (rng!rng_j)) = rng_j)) /\ (Z.of_nat (length rng) = (^ choices))) -> Forall (fun x11 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length rng) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((rng!im) = index)) /\ (((eqs!im) = 0%F) -> ~((rng!im) = index))))) /\ ((length eqs) = (length rng))) -> True -> ((((4%nat < (C.k - 1%nat)%Z) /\ ((^ v) < (2%nat ^ 4%nat)%Z)) /\ (v = choices)) -> True).
Proof. hammer. Qed.

Lemma QuinSelector_obligation8: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (rng : (list F)) (eqs : (list F)) (v : Z), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x12 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> Forall (fun x13 => True) rng -> ((forall (rng_j:nat), 0%nat <= rng_j < (^ choices) -> ((^ (rng!rng_j)) = rng_j)) /\ (Z.of_nat (length rng) = (^ choices))) -> Forall (fun x14 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length rng) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((rng!im) = index)) /\ (((eqs!im) = 0%F) -> ~((rng!im) = index))))) /\ ((length eqs) = (length rng))) -> True -> ((v = (^ choices)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma QuinSelector_obligation9: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (rng : (list F)) (eqs : (list F)) (v : (list F)), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x15 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> Forall (fun x16 => True) rng -> ((forall (rng_j:nat), 0%nat <= rng_j < (^ choices) -> ((^ (rng!rng_j)) = rng_j)) /\ (Z.of_nat (length rng) = (^ choices))) -> Forall (fun x17 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length rng) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((rng!im) = index)) /\ (((eqs!im) = 0%F) -> ~((rng!im) = index))))) /\ ((length eqs) = (length rng))) -> Forall (fun x18 => True) v -> True -> (((Z.of_nat (length v) = (^ choices)) /\ (v = _in)) -> (Z.of_nat (length v) = (^ choices))).
Proof. hammer. Qed.

Lemma QuinSelector_obligation10: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (rng : (list F)) (eqs : (list F)) (v : (list F)), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x19 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> Forall (fun x20 => True) rng -> ((forall (rng_j:nat), 0%nat <= rng_j < (^ choices) -> ((^ (rng!rng_j)) = rng_j)) /\ (Z.of_nat (length rng) = (^ choices))) -> Forall (fun x21 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length rng) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((rng!im) = index)) /\ (((eqs!im) = 0%F) -> ~((rng!im) = index))))) /\ ((length eqs) = (length rng))) -> Forall (fun x22 => True) v -> True -> ((((forall (im:nat), 0%nat <= im < (length rng) -> ((((v!im) = 0%F) \/ ((v!im) = 1%F)) /\ ((((v!im) = 1%F) -> ((rng!im) = index)) /\ (((v!im) = 0%F) -> ~((rng!im) = index))))) /\ ((length v) = (length rng))) /\ (v = eqs)) -> (Z.of_nat (length v) = (^ choices))).
Proof. hammer. Qed.

Lemma QuinSelector_obligation11_trivial: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (rng : (list F)) (eqs : (list F)) (muls : (list F)) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x23 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> Forall (fun x24 => True) rng -> ((forall (rng_j:nat), 0%nat <= rng_j < (^ choices) -> ((^ (rng!rng_j)) = rng_j)) /\ (Z.of_nat (length rng) = (^ choices))) -> Forall (fun x25 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length rng) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((rng!im) = index)) /\ (((eqs!im) = 0%F) -> ~((rng!im) = index))))) /\ ((length eqs) = (length rng))) -> Forall (fun x26 => True) muls -> ((forall (mul_j:nat), 0%nat <= mul_j < (^ choices) -> ((muls!mul_j) = ((_in!mul_j) * (eqs!mul_j))%F)) /\ (Z.of_nat (length muls) = (^ choices))) -> True -> ((((4%nat < (C.k - 1%nat)%Z) /\ ((^ v) < (2%nat ^ 4%nat)%Z)) /\ (v = choices)) -> True).
Proof. hammer. Qed.

Lemma QuinSelector_obligation12: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (rng : (list F)) (eqs : (list F)) (muls : (list F)) (v : Z), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x27 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> Forall (fun x28 => True) rng -> ((forall (rng_j:nat), 0%nat <= rng_j < (^ choices) -> ((^ (rng!rng_j)) = rng_j)) /\ (Z.of_nat (length rng) = (^ choices))) -> Forall (fun x29 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length rng) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((rng!im) = index)) /\ (((eqs!im) = 0%F) -> ~((rng!im) = index))))) /\ ((length eqs) = (length rng))) -> Forall (fun x30 => True) muls -> ((forall (mul_j:nat), 0%nat <= mul_j < (^ choices) -> ((muls!mul_j) = ((_in!mul_j) * (eqs!mul_j))%F)) /\ (Z.of_nat (length muls) = (^ choices))) -> True -> ((v = (^ choices)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma QuinSelector_obligation13: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (rng : (list F)) (eqs : (list F)) (muls : (list F)) (v : (list F)), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x31 => True) _in -> (Z.of_nat (length _in) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> Forall (fun x32 => True) rng -> ((forall (rng_j:nat), 0%nat <= rng_j < (^ choices) -> ((^ (rng!rng_j)) = rng_j)) /\ (Z.of_nat (length rng) = (^ choices))) -> Forall (fun x33 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length rng) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((rng!im) = index)) /\ (((eqs!im) = 0%F) -> ~((rng!im) = index))))) /\ ((length eqs) = (length rng))) -> Forall (fun x34 => True) muls -> ((forall (mul_j:nat), 0%nat <= mul_j < (^ choices) -> ((muls!mul_j) = ((_in!mul_j) * (eqs!mul_j))%F)) /\ (Z.of_nat (length muls) = (^ choices))) -> Forall (fun x35 => True) v -> True -> ((((forall (mul_j:nat), 0%nat <= mul_j < (^ choices) -> ((v!mul_j) = ((_in!mul_j) * (eqs!mul_j))%F)) /\ (Z.of_nat (length v) = (^ choices))) /\ (v = muls)) -> (Z.of_nat (length v) = (^ choices))).
Proof. hammer. Qed.

Lemma QuinSelector_obligation14: forall (choices : F) (_in : (list F)) (index : F) (lt : F) (u0 : unit) (rng : (list F)) (eqs : (list F)) (muls : (list F)) (v : F), ((4%nat < (C.k - 1%nat)%Z) /\ ((^ choices) < (2%nat ^ 4%nat)%Z)) -> Forall (fun x36 => True) _in -> (Z.of_N (N.of_nat (length _in)) = (^ choices)) -> ((^ index) < (^ choices)) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ index) < (^ choices))) /\ ((lt = 0%F) -> ~((^ index) < (^ choices))))) -> (lt = 1%F) -> Forall (fun x37 => True) rng -> ((forall (rng_j:nat), 0%nat <= rng_j < (^ choices) -> ((^ (rng!rng_j)) = rng_j)) /\ (Z.of_N (N.of_nat (length rng)) = (^ choices))) -> Forall (fun x38 => True) eqs -> ((forall (im:nat), 0%nat <= im < (length rng) -> ((((eqs!im) = 0%F) \/ ((eqs!im) = 1%F)) /\ ((((eqs!im) = 1%F) -> ((rng!im) = index)) /\ (((eqs!im) = 0%F) -> ~((rng!im) = index))))) /\ ((length eqs) = (length rng))) -> Forall (fun x39 => True) muls -> ((forall (mul_j:nat), 0%nat <= mul_j < (^ choices) -> ((muls!mul_j) = ((_in!mul_j) * (eqs!mul_j))%F)) /\ (Z.of_N (N.of_nat (length muls)) = (^ choices))) -> True -> ((v = (sum muls)) -> (((^ index) < (^ choices)) -> (v = (_in!Z.to_nat (^ index))))).
Proof.
  intuit; subst.
  clear H0 H2 H5 H7 H9 H11 H13 H16 H20.
  assert (
      Z.of_N (N.of_nat 0) <= Z.of_N (N.of_nat (Z.to_nat (^ index))) < ^ choices
    ). {
    split; try lia.
    rewrite Z_nat_N.
    rewrite Z2N.id; auto.
    apply F_to_Z_nonneg.
  }
  rewrite (sum_one_hot muls (Z.to_nat (^ index))).
  - rewrite H8; auto.
    rewrite <- H17 in H0.
    pose proof (H6 _ H0) as [H' [H'' H''']].
    destruct H'.
    + exfalso. apply H'''; auto.
      rewrite H17 in H0.
      pose proof (H3 _ H0).
      rewrite Z_nat_N in H4.
      rewrite Z2N.id in H4;
        try apply F_to_Z_nonneg.
      apply ReprZ.ReprZUnsigned.F_to_Z_inj; assumption.
    + rewrite H2. apply Fmul_1_r.
  - auto.
  - intros j [H2 H2'].
    rewrite H19 in H2.
    rewrite H8; auto.
    rewrite <- H17 in H2.
    pose proof (H6 _ H2) as [H4 [H4' H4'']].
    destruct H4.
    + rewrite H4. apply Fmul_0_r.
    + apply H4' in H4.
      rewrite H17 in H2.
      pose proof (H3 _ H2).
      hammer.
Qed.

(** IsNegative *)

Lemma IsNegative_obligation0: forall (_in : F) (v : Z), True -> True -> ((v = 254%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma IsNegative_obligation1_trivial: forall (_in : F) (v : F), True -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma IsNegative_obligation2: forall (_in : F) (z : (list F)) (v : (list F)), True -> Forall (fun x0 => ((x0 = 0%F) \/ (x0 = 1%F))) z -> (((as_le_f z) = _in) /\ ((length z) = 254%nat)) -> Forall (fun x1 => ((x1 = 0%F) \/ (x1 = 1%F))) v -> True -> (((((as_le_f v) = _in) /\ ((length v) = 254%nat)) /\ (v = z)) -> ((length v) = 254%nat)).
Proof. hammer. Qed.

Lemma IsNegative_obligation3: forall (_in : F) (z : (list F)) (v : F), True -> Forall (fun x2 => ((x2 = 0%F) \/ (x2 = 1%F))) z -> (((as_le_f z) = _in) /\ ((length z) = 254%nat)) -> True -> (((v = 0%F) \/ (v = 1%F)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma IsNegative_obligation4: forall (_in : F) (z : (list F)) (v : F), True -> Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) z -> (((as_le_f z) = _in) /\ ((length z) = 254%nat)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((Signed.to_Z (as_le_f z)) < 0%nat)) /\ ((v = 0%F) -> ~((Signed.to_Z (as_le_f z)) < 0%nat)))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((Signed.to_Z _in) < 0%nat)) /\ ((v = 0%F) -> ~((Signed.to_Z _in) < 0%nat))))).
Proof. hammer. Qed.

(** ** Random *)

Lemma Random_obligation0: forall (_in : (list F)) (KEY : F) (v : Z), Forall (fun x0 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> True -> ((v = 3%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma Random_obligation1: forall (_in : (list F)) (KEY : F) (v : Z), Forall (fun x1 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> True -> ((v = 4%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma Random_obligation2: forall (_in : (list F)) (KEY : F) (v : Z), Forall (fun x2 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> True -> ((v = 1%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma Random_obligation3: forall (_in : (list F)) (KEY : F) (v : (list F)), Forall (fun x3 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x4 => True) v -> True -> ((((forall (i:nat), 0%nat <= i < (length v) -> ((15%nat < C.q) /\ ((^ (v!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length v) = 3%nat)) /\ (v = _in)) -> ((length v) = 3%nat)).
Proof. hammer. Qed.

Lemma Random_obligation4_trivial: forall (_in : (list F)) (KEY : F) (v : F), Forall (fun x5 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> True -> ((((15%nat < C.q) /\ ((^ v) < (2%nat ^ 32%nat)%Z)) /\ (v = KEY)) -> True).
Proof. hammer. Qed.

Lemma Random_obligation5: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (v : Z), Forall (fun x6 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x7 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> True -> ((v = 254%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma Random_obligation6_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (v : F), Forall (fun x8 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x9 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> True -> (((v = (mimc!0%nat)) /\ (v = z)) -> True).
Proof. hammer. Qed.

Lemma Random_obligation7_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x10 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x11 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x12 => ((x12 = 0%F) \/ (x12 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = 8%F) -> True).
Proof. hammer. Qed.

Lemma Random_obligation8_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x13 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x14 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x15 => ((x15 = 0%F) \/ (x15 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = (n2b!3%nat)) -> True).
Proof. hammer. Qed.

Lemma Random_obligation9_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x16 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x17 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x18 => ((x18 = 0%F) \/ (x18 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = (8%F * (n2b!3%nat))%F) -> True).
Proof. hammer. Qed.

Lemma Random_obligation10_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x19 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x20 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x21 => ((x21 = 0%F) \/ (x21 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = 4%F) -> True).
Proof. hammer. Qed.

Lemma Random_obligation11_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x22 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x23 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x24 => ((x24 = 0%F) \/ (x24 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = (n2b!2%nat)) -> True).
Proof. hammer. Qed.

Lemma Random_obligation12_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x25 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x26 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x27 => ((x27 = 0%F) \/ (x27 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = (4%F * (n2b!2%nat))%F) -> True).
Proof. hammer. Qed.

Lemma Random_obligation13_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x28 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x29 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x30 => ((x30 = 0%F) \/ (x30 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = 2%F) -> True).
Proof. hammer. Qed.

Lemma Random_obligation14_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x31 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x32 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x33 => ((x33 = 0%F) \/ (x33 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = (n2b!1%nat)) -> True).
Proof. hammer. Qed.

Lemma Random_obligation15_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x34 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x35 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x36 => ((x36 = 0%F) \/ (x36 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = (2%F * (n2b!1%nat))%F) -> True).
Proof. hammer. Qed.

Lemma Random_obligation16_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x37 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x38 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x39 => ((x39 = 0%F) \/ (x39 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = (n2b!0%nat)) -> True).
Proof. hammer. Qed.

Lemma Random_obligation17_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x40 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x41 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x42 => ((x42 = 0%F) \/ (x42 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = ((2%F * (n2b!1%nat))%F + (n2b!0%nat))%F) -> True).
Proof. hammer. Qed.

Lemma Random_obligation18_trivial: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x43 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x44 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x45 => ((x45 = 0%F) \/ (x45 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = ((4%F * (n2b!2%nat))%F + ((2%F * (n2b!1%nat))%F + (n2b!0%nat))%F)%F) -> True).
Proof. hammer. Qed.

Lemma Random_obligation19: forall (_in : (list F)) (KEY : F) (mimc : (list F)) (z : F) (n2b : (list F)) (v : F), Forall (fun x46 => True) _in -> ((forall (i:nat), 0%nat <= i < (length _in) -> ((15%nat < C.q) /\ ((^ (_in!i)) < (2%nat ^ 32%nat)%Z))) /\ ((length _in) = 3%nat)) -> ((15%nat < C.q) /\ ((^ KEY) < (2%nat ^ 32%nat)%Z)) -> Forall (fun x47 => True) mimc -> ((mimc = (MiMCSponge 3%nat 4%nat 1%nat _in KEY)) /\ ((length mimc) = 1%nat)) -> (z = (mimc!0%nat)) -> Forall (fun x48 => ((x48 = 0%F) \/ (x48 = 1%F))) n2b -> (((as_le_f n2b) = z) /\ ((length n2b) = 254%nat)) -> True -> ((v = ((8%F * (n2b!3%nat))%F + ((4%F * (n2b!2%nat))%F + ((2%F * (n2b!1%nat))%F + (n2b!0%nat))%F)%F)%F) -> ((^ v) <= 15%nat)).
Proof.
  unwrap_C; intros; subst; destruct H1, H6.
  assert (^n2b ! 0 <= 1). apply Repr.in_range_binary; auto.
  assert (^n2b ! 1 <= 1). apply Repr.in_range_binary; auto.
  assert (^n2b ! 2 <= 1). apply Repr.in_range_binary; auto.
  assert (^n2b ! 3 <= 1). apply Repr.in_range_binary; auto.
  repeat (autorewrite with F_to_Z; pose_nonneg; try (lia || nia)).
Qed.

(** ** RangeProof *)

Lemma RangeProof_obligation0_trivial: forall (bits : Z) (max_abs_value : F) (_in : F) (v : F), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> True -> ((((^ (max_abs_value + v)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) /\ (v = _in)) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation1_trivial: forall (bits : Z) (max_abs_value : F) (_in : F) (v : F), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> True -> ((v = 2%F) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation2: forall (bits : Z) (max_abs_value : F) (_in : F) (v : Z), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> True -> ((((0%nat < v) /\ ((v + 1%nat)%Z <= (C.k - 1%nat)%Z)) /\ (v = bits)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma RangeProof_obligation3_trivial: forall (bits : Z) (max_abs_value : F) (_in : F) (v : F), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> True -> ((v = (2%F ^ Z.to_N bits)%F) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation4_trivial: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (v : Z), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> True -> ((((0%nat < v) /\ ((v + 1%nat)%Z <= (C.k - 1%nat)%Z)) /\ (v = bits)) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation5_trivial: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (v : Z), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> True -> ((v = 1%nat) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation6: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (v : Z), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> True -> ((v = (bits + 1%nat)%Z) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma RangeProof_obligation7_trivial: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (v : F), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> True -> (((v = (_in + (2%F ^ Z.to_N bits)%F)%F) /\ (v = x)) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation8: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (n2b1 : (list F)) (v : Z), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> Forall (fun x0 => ((x0 = 0%F) \/ (x0 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ ((length n2b1) = Z.to_nat (bits + 1%nat)%Z)) -> True -> ((((0%nat < v) /\ ((v + 1%nat)%Z <= (C.k - 1%nat)%Z)) /\ (v = bits)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma RangeProof_obligation9_trivial: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (n2b1 : (list F)) (v : F), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> Forall (fun x1 => ((x1 = 0%F) \/ (x1 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ ((length n2b1) = Z.to_nat (bits + 1%nat)%Z)) -> True -> ((((0%nat <= (Signed.to_Z v)) /\ ((^ (2%F * v)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) /\ (v = max_abs_value)) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation10_trivial: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (v : Z), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> Forall (fun x2 => ((x2 = 0%F) \/ (x2 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ ((length n2b1) = Z.to_nat (bits + 1%nat)%Z)) -> Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ ((length n2b2) = Z.to_nat bits)) -> True -> ((((0%nat < v) /\ ((v + 1%nat)%Z <= (C.k - 1%nat)%Z)) /\ (v = bits)) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation11_trivial: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (v : Z), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> Forall (fun x4 => ((x4 = 0%F) \/ (x4 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ ((length n2b1) = Z.to_nat (bits + 1%nat)%Z)) -> Forall (fun x5 => ((x5 = 0%F) \/ (x5 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ ((length n2b2) = Z.to_nat bits)) -> True -> ((v = 1%nat) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation12: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (v : Z), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> Forall (fun x6 => ((x6 = 0%F) \/ (x6 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ ((length n2b1) = Z.to_nat (bits + 1%nat)%Z)) -> Forall (fun x7 => ((x7 = 0%F) \/ (x7 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ ((length n2b2) = Z.to_nat bits)) -> True -> ((v = (bits + 1%nat)%Z) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof. hammer. Qed.

Lemma RangeProof_obligation13_trivial: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (v : F), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> Forall (fun x8 => ((x8 = 0%F) \/ (x8 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ ((length n2b1) = Z.to_nat (bits + 1%nat)%Z)) -> Forall (fun x9 => ((x9 = 0%F) \/ (x9 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ ((length n2b2) = Z.to_nat bits)) -> True -> ((((0%nat <= (Signed.to_Z v)) /\ ((^ (2%F * v)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) /\ (v = max_abs_value)) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation14_trivial: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (v : F), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> Forall (fun x10 => ((x10 = 0%F) \/ (x10 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ ((length n2b1) = Z.to_nat (bits + 1%nat)%Z)) -> Forall (fun x11 => ((x11 = 0%F) \/ (x11 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ ((length n2b2) = Z.to_nat bits)) -> True -> ((((^ (max_abs_value + v)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) /\ (v = _in)) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation15: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (v : F), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> Forall (fun x12 => ((x12 = 0%F) \/ (x12 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ ((length n2b1) = Z.to_nat (bits + 1%nat)%Z)) -> Forall (fun x13 => ((x13 = 0%F) \/ (x13 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ ((length n2b2) = Z.to_nat bits)) -> True -> ((v = (max_abs_value + _in)%F) -> ((^ v) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)).
Proof. hammer. Qed.

Lemma RangeProof_obligation16: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (v : F), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> Forall (fun x14 => ((x14 = 0%F) \/ (x14 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ ((length n2b1) = Z.to_nat (bits + 1%nat)%Z)) -> Forall (fun x15 => ((x15 = 0%F) \/ (x15 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ ((length n2b2) = Z.to_nat bits)) -> True -> ((v = 0%F) -> ((^ v) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)).
Proof.
  intuit; subst; simpl in *.
  rewrite Zmod_0_l. lia.
Qed.

Lemma RangeProof_obligation17_trivial: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (v : Z), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> Forall (fun x16 => ((x16 = 0%F) \/ (x16 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ ((length n2b1) = Z.to_nat (bits + 1%nat)%Z)) -> Forall (fun x17 => ((x17 = 0%F) \/ (x17 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ ((length n2b2) = Z.to_nat bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> True -> ((((0%nat < v) /\ ((v + 1%nat)%Z <= (C.k - 1%nat)%Z)) /\ (v = bits)) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation18_trivial: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (v : Z), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> Forall (fun x18 => ((x18 = 0%F) \/ (x18 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ ((length n2b1) = Z.to_nat (bits + 1%nat)%Z)) -> Forall (fun x19 => ((x19 = 0%F) \/ (x19 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ ((length n2b2) = Z.to_nat bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> True -> ((v = 1%nat) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation19: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (v : Z), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> Forall (fun x20 => ((x20 = 0%F) \/ (x20 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ ((length n2b1) = Z.to_nat (bits + 1%nat)%Z)) -> Forall (fun x21 => ((x21 = 0%F) \/ (x21 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ ((length n2b2) = Z.to_nat bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> True -> ((v = (bits + 1%nat)%Z) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof. hammer. Qed.

Lemma RangeProof_obligation20_trivial: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (v : F), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> Forall (fun x22 => ((x22 = 0%F) \/ (x22 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ ((length n2b1) = Z.to_nat (bits + 1%nat)%Z)) -> Forall (fun x23 => ((x23 = 0%F) \/ (x23 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ ((length n2b2) = Z.to_nat bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> True -> ((v = 2%F) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation21_trivial: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (v : F), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> Forall (fun x24 => ((x24 = 0%F) \/ (x24 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ ((length n2b1) = Z.to_nat (bits + 1%nat)%Z)) -> Forall (fun x25 => ((x25 = 0%F) \/ (x25 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ ((length n2b2) = Z.to_nat bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> True -> ((((0%nat <= (Signed.to_Z v)) /\ ((^ (2%F * v)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) /\ (v = max_abs_value)) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation22: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (v : F), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> Forall (fun x26 => ((x26 = 0%F) \/ (x26 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ ((length n2b1) = Z.to_nat (bits + 1%nat)%Z)) -> Forall (fun x27 => ((x27 = 0%F) \/ (x27 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ ((length n2b2) = Z.to_nat bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> True -> ((v = (2%F * max_abs_value)%F) -> ((^ v) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)).
Proof. hammer. Qed.

Lemma RangeProof_obligation23_trivial: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (v : F), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> Forall (fun x28 => ((x28 = 0%F) \/ (x28 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ ((length n2b1) = Z.to_nat (bits + 1%nat)%Z)) -> Forall (fun x29 => ((x29 = 0%F) \/ (x29 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ ((length n2b2) = Z.to_nat bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> True -> ((((0%nat <= (Signed.to_Z v)) /\ ((^ (2%F * v)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) /\ (v = max_abs_value)) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation24_trivial: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (v : F), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> Forall (fun x30 => ((x30 = 0%F) \/ (x30 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ ((length n2b1) = Z.to_nat (bits + 1%nat)%Z)) -> Forall (fun x31 => ((x31 = 0%F) \/ (x31 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ ((length n2b2) = Z.to_nat bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> True -> ((((^ (max_abs_value + v)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) /\ (v = _in)) -> True).
Proof. hammer. Qed.

Lemma RangeProof_obligation25: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (v : F), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> Forall (fun x32 => ((x32 = 0%F) \/ (x32 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ ((length n2b1) = Z.to_nat (bits + 1%nat)%Z)) -> Forall (fun x33 => ((x33 = 0%F) \/ (x33 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ ((length n2b2) = Z.to_nat bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> True -> ((v = (max_abs_value + _in)%F) -> ((^ v) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)).
Proof. hammer. Qed.

Lemma RangeProof_obligation26_trivial: forall (bits : Z) (max_abs_value : F) (_in : F) (x : F) (n2b1 : (list F)) (n2b2 : (list F)) (lt1 : F) (u0 : unit) (lt2 : F) (v : unit), ((0%nat < bits) /\ ((bits + 1%nat)%Z <= (C.k - 1%nat)%Z)) -> ((0%nat <= (Signed.to_Z max_abs_value)) /\ ((^ (2%F * max_abs_value)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z)) -> ((^ (max_abs_value + _in)%F) <= ((2%nat ^ (bits + 1%nat)%Z)%Z - 1%nat)%Z) -> (x = (_in + (2%F ^ Z.to_N bits)%F)%F) -> Forall (fun x34 => ((x34 = 0%F) \/ (x34 = 1%F))) n2b1 -> (((as_le_f n2b1) = x) /\ ((length n2b1) = Z.to_nat (bits + 1%nat)%Z)) -> Forall (fun x35 => ((x35 = 0%F) \/ (x35 = 1%F))) n2b2 -> (((as_le_f n2b2) = max_abs_value) /\ ((length n2b2) = Z.to_nat bits)) -> (((lt1 = 0%F) \/ (lt1 = 1%F)) /\ (((lt1 = 1%F) -> ((^ (max_abs_value + _in)%F) < (^ 0%F))) /\ ((lt1 = 0%F) -> ~((^ (max_abs_value + _in)%F) < (^ 0%F))))) -> (lt1 = 0%F) -> (((lt2 = 0%F) \/ (lt2 = 1%F)) /\ (((lt2 = 1%F) -> ((^ (2%F * max_abs_value)%F) < (^ (max_abs_value + _in)%F))) /\ ((lt2 = 0%F) -> ~((^ (2%F * max_abs_value)%F) < (^ (max_abs_value + _in)%F))))) -> True -> ((lt2 = 0%F) -> True).
Proof. hammer. Qed.
