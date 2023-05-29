(** * DSL benchmark: ZK-ML *)

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

From Circom Require Import Circom Util Default Tuple ListUtil LibTactics Simplify Repr Signed Coda.
From Circom.CircomLib Require Import Bitify.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

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

(** ** IsNegative *)

Lemma IsNegative_obligation0: forall (_in : F) (v : Z), True -> True -> ((v = 254%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma IsNegative_obligation1_trivial: forall (_in : F) (v : F), True -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma IsNegative_obligation2: forall (_in : F) (n2b : (list F)) (v : (list F)), True -> Forall (fun x0 => ((x0 = 0%F) \/ (x0 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> Forall (fun x1 => ((x1 = 0%F) \/ (x1 = 1%F))) v -> True -> (((((as_le_f v) = _in) /\ ((length v) = 254%nat)) /\ (v = n2b)) -> ((length v) = 254%nat)).
Proof. hammer. Qed.

Lemma IsNegative_obligation3: forall (_in : F) (n2b : (list F)) (v : F), True -> Forall (fun x2 => ((x2 = 0%F) \/ (x2 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> True -> (((v = 0%F) \/ (v = 1%F)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma IsNegative_obligation4: forall (_in : F) (n2b : (list F)) (v : F), True -> Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((v = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((Signed.to_Z _in) < 0%nat)) /\ ((v = 0%F) -> ~((Signed.to_Z _in) < 0%nat))))).
Proof. hammer. Qed.

(** ** IsPositive (fixed) *)

Lemma IsPositive_obligation0: forall (_in : F) (v : Z), True -> True -> ((v = 254%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma IsPositive_obligation1_trivial: forall (_in : F) (v : F), True -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma IsPositive_obligation2: forall (_in : F) (n2b : (list F)) (v : (list F)), True -> Forall (fun x4 => ((x4 = 0%F) \/ (x4 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> Forall (fun x5 => ((x5 = 0%F) \/ (x5 = 1%F))) v -> True -> (((((as_le_f v) = _in) /\ ((length v) = 254%nat)) /\ (v = n2b)) -> ((length v) = 254%nat)).
Proof. hammer. Qed.

Lemma IsPositive_obligation3: forall (_in : F) (n2b : (list F)) (v : F), True -> Forall (fun x6 => ((x6 = 0%F) \/ (x6 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> True -> (((v = 0%F) \/ (v = 1%F)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma IsPositive_obligation4_trivial: forall (_in : F) (n2b : (list F)) (s : F) (v : F), True -> Forall (fun x7 => ((x7 = 0%F) \/ (x7 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> (((s = 0%F) \/ (s = 1%F)) /\ (((s = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((s = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma IsPositive_obligation5_trivial: forall (_in : F) (n2b : (list F)) (s : F) (isz : F) (v : F), True -> Forall (fun x8 => ((x8 = 0%F) \/ (x8 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> (((s = 0%F) \/ (s = 1%F)) /\ (((s = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((s = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> True -> ((v = 1%F) -> True).
Proof. hammer. Qed.

Lemma IsPositive_obligation6_trivial: forall (_in : F) (n2b : (list F)) (s : F) (isz : F) (v : F), True -> Forall (fun x9 => ((x9 = 0%F) \/ (x9 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> (((s = 0%F) \/ (s = 1%F)) /\ (((s = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((s = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> True -> (((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((v = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) /\ (v = s)) -> True).
Proof. hammer. Qed.

Lemma IsPositive_obligation7_trivial: forall (_in : F) (n2b : (list F)) (s : F) (isz : F) (v : F), True -> Forall (fun x10 => ((x10 = 0%F) \/ (x10 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> (((s = 0%F) \/ (s = 1%F)) /\ (((s = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((s = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> True -> ((v = (1%F - s)%F) -> True).
Proof. hammer. Qed.

Lemma IsPositive_obligation8_trivial: forall (_in : F) (n2b : (list F)) (s : F) (isz : F) (v : F), True -> Forall (fun x11 => ((x11 = 0%F) \/ (x11 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> (((s = 0%F) \/ (s = 1%F)) /\ (((s = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((s = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> True -> ((v = 1%F) -> True).
Proof. hammer. Qed.

Lemma IsPositive_obligation9_trivial: forall (_in : F) (n2b : (list F)) (s : F) (isz : F) (v : F), True -> Forall (fun x12 => ((x12 = 0%F) \/ (x12 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> (((s = 0%F) \/ (s = 1%F)) /\ (((s = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((s = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> True -> (((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (_in = 0%F)) /\ ((v = 0%F) -> ~(_in = 0%F)))) /\ (v = isz)) -> True).
Proof. hammer. Qed.

Lemma IsPositive_obligation10_trivial: forall (_in : F) (n2b : (list F)) (s : F) (isz : F) (v : F), True -> Forall (fun x13 => ((x13 = 0%F) \/ (x13 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> (((s = 0%F) \/ (s = 1%F)) /\ (((s = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((s = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> True -> ((v = (1%F - isz)%F) -> True).
Proof. hammer. Qed.

Lemma IsPositive_obligation11: forall (_in : F) (n2b : (list F)) (s : F) (isz : F) (v : F), True -> Forall (fun x14 => ((x14 = 0%F) \/ (x14 = 1%F))) n2b -> (((as_le_f n2b) = _in) /\ ((length n2b) = 254%nat)) -> (((s = 0%F) \/ (s = 1%F)) /\ (((s = 1%F) -> ((Signed.to_Z (as_le_f n2b)) < 0%nat)) /\ ((s = 0%F) -> ~((Signed.to_Z (as_le_f n2b)) < 0%nat)))) -> (((isz = 0%F) \/ (isz = 1%F)) /\ (((isz = 1%F) -> (_in = 0%F)) /\ ((isz = 0%F) -> ~(_in = 0%F)))) -> True -> ((v = ((1%F - s)%F * (1%F - isz)%F)%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (0%nat < (Signed.to_Z _in))) /\ ((v = 0%F) -> ~(0%nat < (Signed.to_Z _in)))))).
Proof.
  unwrap_C; intuit; subst;
    try lia; try fqsatz;
    try (left; fqsatz);
    try (right; fqsatz).
  - destruct (dec (as_le_f n2b = 0)%F);subst;try easy.
    unfold Signed.to_Z. destruct dec.
    + simpl in *. pose proof (F_to_Z_nonneg (as_le_f n2b)).
      assert(^ as_le_f n2b <> 0).
      { apply F.to_Z_nonzero;auto. }
      lia.
    + simpl in *. 
      unfold Signed.to_Z in H2. destruct dec;try easy.
      assert(q <= ^ as_le_f n2b).
      { lia. } 
      destruct (dec (Zpos q = ^ as_le_f n2b)%Z);try lia.
      pose proof (F.to_Z_range (as_le_f n2b)). lia.
  - rewrite H10 in H12.
    unfold Signed.to_Z in H12.
    destruct dec;simpl in H12;try fqsatz.
    rewrite Z.mod_small in H12;try lia.
    apply n. simpl. lia.
Qed.

(** ** ReLU *)

Lemma ReLU_obligation0_trivial: forall (_in : F) (v : F), True -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma ReLU_obligation1_trivial: forall (_in : F) (isp : F) (v : F), True -> (((isp = 0%F) \/ (isp = 1%F)) /\ (((isp = 1%F) -> (0%nat < (Signed.to_Z _in))) /\ ((isp = 0%F) -> ~(0%nat < (Signed.to_Z _in))))) -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma ReLU_obligation2_trivial: forall (_in : F) (isp : F) (v : F), True -> (((isp = 0%F) \/ (isp = 1%F)) /\ (((isp = 1%F) -> (0%nat < (Signed.to_Z _in))) /\ ((isp = 0%F) -> ~(0%nat < (Signed.to_Z _in))))) -> True -> (((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (0%nat < (Signed.to_Z _in))) /\ ((v = 0%F) -> ~(0%nat < (Signed.to_Z _in))))) /\ (v = isp)) -> True).
Proof. hammer. Qed.

Lemma ReLU_obligation3: forall (_in : F) (isp : F) (v : F), True -> (((isp = 0%F) \/ (isp = 1%F)) /\ (((isp = 1%F) -> (0%nat < (Signed.to_Z _in))) /\ ((isp = 0%F) -> ~(0%nat < (Signed.to_Z _in))))) -> True -> ((v = (_in * isp)%F) -> ((Signed.to_Z v) = (Z.max 0%nat (Signed.to_Z _in)))).
Proof.
  intros; intuit; subst; simpl in *.
  - assert ($ _in <= 0) by lia.
    rewrite Z.max_l; auto.
    rewrite Fmul_0_r.
    apply Signed.to_Z_0.
  - rewrite Z.max_r; try lia.
    rewrite Fmul_1_r; auto.
Qed.

(** ** Poly *)

Lemma Poly_obligation0_trivial: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma Poly_obligation1_trivial: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma Poly_obligation2_trivial: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = (_in * _in)%F) -> True).
Proof. hammer. Qed.

Lemma Poly_obligation3_trivial: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = n) -> True).
Proof. hammer. Qed.

Lemma Poly_obligation4_trivial: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = _in) -> True).
Proof. hammer. Qed.

Lemma Poly_obligation5_trivial: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = (n * _in)%F) -> True).
Proof. hammer. Qed.

Lemma Poly_obligation6: forall (n : F) (_in : F) (v : F), True -> True -> True -> ((v = ((_in * _in)%F + (n * _in)%F)%F) -> (v = (_in * (_in + n)%F)%F)).
Proof.
  unwrap_C; intros; fqsatz.
Qed.

Definition Fmax (x y: F) := if dec (^x > ^y) then x else y.

Fixpoint fmax (xs: list F) : F :=
  match xs with
  | nil => default
  | x::xs' =>
    let m := fmax xs' in Fmax x m
  end.

Lemma fmax_first1: forall xs, 1 <= length xs -> fmax (xs[:1]) = xs!0.
Proof.
  destruct xs. simpl. lia.
  unfold_default.  simpl. 
  unfold Fmax. pose_nonneg. split_dec.
  auto.
  autorewrite with F_to_Z in n; try lia.
  assert (^f = 0) by lia.
  rewrite <- (@F.to_Z_0 q) in H.
  apply ReprZ.ReprZUnsigned.F_to_Z_inj in H.
  auto.
Qed.


Lemma Fmax_comm: forall x y, Fmax x y = Fmax y x.
Proof. intros. unfold Fmax; pose_nonneg. split_dec; try lia; try auto.
  apply ReprZ.ReprZUnsigned.F_to_Z_inj. lia. Qed.


Lemma Fmax_0_l: forall x, Fmax 0 x = x.
Proof. intros. unfold Fmax; pose_nonneg. split_dec.
  autorewrite with F_to_Z in g. exfalso. lia.
  auto.
Qed.

Lemma Fmax_0_r: forall x, Fmax x 0 = x.
Proof.
  intros. rewrite Fmax_comm. apply Fmax_0_l.
Qed.

Lemma fmax_app: forall xs ys, fmax (xs ++ ys) = Fmax (fmax xs) (fmax ys).
Proof.
  induction xs; simpl; intros.
  rewrite Fmax_0_l. auto.
  rewrite IHxs.
  unfold Fmax. split_dec; (auto || lia).
Qed.


Lemma fmax_spec: forall xs, Forall (fun x => ^x <= ^fmax xs) xs.
Proof. Admitted.

Lemma Fmax_left: forall x y, ^x >= ^y -> Fmax x y = x.
Proof. Admitted.
Lemma Fmax_right: forall x y, ^x <= ^y -> Fmax x y = y.
Proof. Admitted.

Lemma Max_obligation0_trivial: forall (n : nat) (_in : (list F)) (v : Z), ((1%nat <= n) /\ ((n <= (C.k - 1%nat)%Z) /\ True)) -> Forall (fun x15 => ((^ x15) <= ((2%nat ^ n)%Z - 1%nat)%Z)) _in -> ((length _in) = n) -> True -> ((v = 1%nat) -> True).
Proof. hammer. Qed.

Lemma Max_obligation1_trivial: forall (n : nat) (_in : (list F)) (v : Z), ((1%nat <= n) /\ ((n <= (C.k - 1%nat)%Z) /\ True)) -> Forall (fun x16 => ((^ x16) <= ((2%nat ^ n)%Z - 1%nat)%Z)) _in -> ((length _in) = n) -> True -> ((((0%nat <= v) /\ ((1%nat <= v) /\ ((v <= (C.k - 1%nat)%Z) /\ True))) /\ (v = n)) -> True).
Proof. hammer. Qed.

Lemma Max_obligation2: forall (n : nat) (_in : (list F)) (v : Z), ((1%nat <= n) /\ ((n <= (C.k - 1%nat)%Z) /\ True)) -> Forall (fun x17 => ((^ x17) <= ((2%nat ^ n)%Z - 1%nat)%Z)) _in -> ((length _in) = n) -> True -> (((1%nat <= v) /\ (v < n)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma Max_obligation3_trivial: forall (n : nat) (_in : (list F)) (i : nat) (v : F), ((1%nat <= n) /\ ((n <= (C.k - 1%nat)%Z) /\ True)) -> Forall (fun x18 => ((^ x18) <= ((2%nat ^ n)%Z - 1%nat)%Z)) _in -> ((length _in) = n) -> ((1%nat <= i) /\ (i < n)) -> True -> (((v = (fmax (_in[:(i + 1%nat)%nat]))) /\ (((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ True)) -> True).
Proof. hammer. Qed.

Lemma Max_obligation4: forall (n : nat) (_in : (list F)) (i : nat) (max : F) (v : Z), ((1%nat <= n) /\ ((n <= (C.k - 1%nat)%Z) /\ True)) -> Forall (fun x19 => ((^ x19) <= ((2%nat ^ n)%Z - 1%nat)%Z)) _in -> ((length _in) = n) -> ((1%nat <= i) /\ (i < n)) -> ((max = (fmax (_in[:(i + 1%nat)%nat]))) /\ (((^ max) <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ True)) -> True -> ((((0%nat <= v) /\ ((1%nat <= v) /\ ((v <= (C.k - 1%nat)%Z) /\ True))) /\ (v = n)) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof. hammer. Qed.

Lemma Max_obligation5: forall (n : nat) (_in : (list F)) (i : nat) (max : F) (v : F), ((1%nat <= n) /\ ((n <= (C.k - 1%nat)%Z) /\ True)) -> Forall (fun x20 => ((^ x20) <= ((2%nat ^ n)%Z - 1%nat)%Z)) _in -> ((length _in) = n) -> ((1%nat <= i) /\ (i < n)) -> ((max = (fmax (_in[:(i + 1%nat)%nat]))) /\ (((^ max) <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ True)) -> True -> ((v = (_in!i)) -> ((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z)).
Proof. hammer. Qed.

Lemma Max_obligation6: forall (n : nat) (_in : (list F)) (i : nat) (max : F) (v : F), ((1%nat <= n) /\ ((n <= (C.k - 1%nat)%Z) /\ True)) -> Forall (fun x21 => ((^ x21) <= ((2%nat ^ n)%Z - 1%nat)%Z)) _in -> ((length _in) = n) -> ((1%nat <= i) /\ (i < n)) -> ((max = (fmax (_in[:(i + 1%nat)%nat]))) /\ (((^ max) <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ True)) -> True -> ((((v = (fmax (_in[:(i + 1%nat)%nat]))) /\ (((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ True)) /\ (v = max)) -> ((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z)).
Proof. hammer. Qed.

Lemma Max_obligation7: forall (n : nat) (_in : (list F)) (i : nat) (max : F) (gt : F) (v : F), ((1%nat <= n) /\ ((n <= (C.k - 1%nat)%Z) /\ True)) -> Forall (fun x22 => ((^ x22) <= ((2%nat ^ n)%Z - 1%nat)%Z)) _in -> ((length _in) = n) -> ((1%nat <= i) /\ (i < n)) -> ((max = (fmax (_in[:(i + 1%nat)%nat]))) /\ (((^ max) <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ True)) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ max) < (^ (_in!i)))) /\ ((gt = 0%F) -> ~((^ max) < (^ (_in!i)))))) -> True -> (((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((^ max) < (^ (_in!i)))) /\ ((v = 0%F) -> ~((^ max) < (^ (_in!i)))))) /\ (v = gt)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma Max_obligation8_trivial: forall (n : nat) (_in : (list F)) (i : nat) (max : F) (gt : F) (v : F), ((1%nat <= n) /\ ((n <= (C.k - 1%nat)%Z) /\ True)) -> Forall (fun x23 => ((^ x23) <= ((2%nat ^ n)%Z - 1%nat)%Z)) _in -> ((length _in) = n) -> ((1%nat <= i) /\ (i < n)) -> ((max = (fmax (_in[:(i + 1%nat)%nat]))) /\ (((^ max) <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ True)) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ max) < (^ (_in!i)))) /\ ((gt = 0%F) -> ~((^ max) < (^ (_in!i)))))) -> True -> ((((v = (fmax (_in[:(i + 1%nat)%nat]))) /\ (((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ True)) /\ (v = max)) -> True).
Proof. hammer. Qed.

Lemma Max_obligation9_trivial: forall (n : nat) (_in : (list F)) (i : nat) (max : F) (gt : F) (v : F), ((1%nat <= n) /\ ((n <= (C.k - 1%nat)%Z) /\ True)) -> Forall (fun x24 => ((^ x24) <= ((2%nat ^ n)%Z - 1%nat)%Z)) _in -> ((length _in) = n) -> ((1%nat <= i) /\ (i < n)) -> ((max = (fmax (_in[:(i + 1%nat)%nat]))) /\ (((^ max) <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ True)) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ max) < (^ (_in!i)))) /\ ((gt = 0%F) -> ~((^ max) < (^ (_in!i)))))) -> True -> ((v = (_in!i)) -> True).
Proof. hammer. Qed.


Lemma Max_obligation10: forall (n : nat) (_in : (list F)) (i : nat) (max : F) (gt : F) (v : F), ((1%nat <= n) /\ ((n <= (C.k - 1%nat)%Z) /\ True)) -> Forall (fun x25 => ((^ x25) <= ((2%nat ^ n)%Z - 1%nat)%Z)) _in -> ((length _in) = n) -> ((1%nat <= i) /\ (i < n)) -> ((max = (fmax (_in[:i]))) /\ (((^ max) <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ True)) -> (((gt = 0%F) \/ (gt = 1%F)) /\ (((gt = 1%F) -> ((^ max) < (^ (_in!i)))) /\ ((gt = 0%F) -> ~((^ max) < (^ (_in!i)))))) -> True -> ((((gt = 0%F) -> (v = max)) /\ (~((gt = 0%F)) -> (v = (_in!i)))) -> ((v = (fmax (_in[:(i + 1%nat)%nat]))) /\ (((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ True))).
Proof.
  intros. 
  intuit; subst v; try auto; symmetry in H2.
  - rewrite firstn_plus1 by lia. rewrite fmax_app. 
  rewrite Fmax_left. auto. simpl. rewrite Fmax_0_r. rewrite H2. lia.
  - rewrite firstn_plus1 by lia. rewrite fmax_app. 

  rewrite Fmax_right. simpl. rewrite Fmax_0_r. auto.
    simpl. rewrite Fmax_0_r. auto. rewrite H2. lia.
  Qed.
Lemma Max_obligation11: forall (n : nat) (_in : (list F)) (v : F), ((1%nat <= n) /\ ((n <= (C.k - 1%nat)%Z) /\ True)) -> Forall (fun x26 => ((^ x26) <= ((2%nat ^ n)%Z - 1%nat)%Z)) _in -> ((length _in) = n) -> True -> ((v = (_in!0%nat)) -> ((v = (fmax (_in[:1%nat]))) /\ (((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ True))).
Proof. 
    simplify. intros. intuit.
    rewrite fmax_first1 by lia. auto. 
    subst v. auto.
Qed.


Lemma Max_obligation12: forall (n : nat) (_in : (list F)) (v : F), ((1%nat <= n) /\ ((n <= (C.k - 1%nat)%Z) /\ True)) -> Forall (fun x27 => ((^ x27) <= ((2%nat ^ n)%Z - 1%nat)%Z)) _in -> ((length _in) = n) -> True -> (((v = (fmax (_in[:n]))) /\ (((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z) /\ True)) -> (v = (fmax _in))).
Proof. 
  intros. rewrite firstn_all2 in H3 by lia. intuition.
Qed.
