(** * DSL benchmark: BigLessThan *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.
Require Import Coq.Bool.Bool.

Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Arithmetic.PrimeFieldTheorems.

Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Ring.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

From Circom Require Import Circom Default Util DSL Tuple ListUtil LibTactics Simplify.
From Circom Require Import Repr ReprZ Coda.
From Circom.CircomLib Require Import Bitify Comparators Gates.

Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

(* interpret a tuple of weights as representing a little-endian base-2^n number *)
Local Notation "[| xs | n ]" := (RZ.as_le n xs).
Local Notation "[\ xs \ n ]" := (RZ.as_be n xs).

Lemma big_lt_step: forall xs ys i n,
[\ xs[:i+1] \n] < [\ ys[:i+1] \n] <->
  ([\ xs[:i] \n] < [\ ys[:i] \n] \/
  [\ xs[:i] \n] = [\ ys[:i] \n] /\
  ^(xs!i) < ^(ys!i)).
Proof.
Admitted.

Lemma big_eq_step: forall xs ys i n,
[\ xs[:i+1] \n] = [\ ys[:i+1] \n] <->
  ([\ xs[:i] \n] = [\ ys[:i] \n] /\
  ^(xs!i) = ^(ys!i)).
Proof.
Admitted.


#[local]Hint Extern 10 (Forall _ (firstn _ _)) => apply Forall_firstn : core.
#[local]Hint Extern 10  => match goal with
   | [ |- context[List_nth_Default _ _] ] => unfold_default end: core.
   #[local]Hint Extern 10  => match goal with
   | [ |- context[List.nth  _ _ _] ] => apply Forall_nth end: core.
#[local]Hint Extern 10 => match goal with 
  [ |- context[length _] ] => rewrite_length end : core.
#[local]Hint Extern 10 (Forall _ (skipn _ _)) => apply Forall_skipn : core.
#[local]Hint Extern 10 (Forall _ (rev _)) => apply Forall_rev : core.
#[local]Hint Extern 10 (Forall _ (_ :: _)) => constructor : core.
#[local]Hint Extern 10 (Z.of_N (N.of_nat _)) => rewrite nat_N_Z : core.
#[local]Hint Extern 10  => repeat match goal with
  [ H: context[Z.of_N (N.of_nat _)] |- _] => rewrite nat_N_Z in H end : core.
  #[local]Hint Extern 10  => repeat match goal with
  [ |- context[length (rev _)] ] => rewrite rev_length end : core.
#[local]Hint Extern 10 (_ < _) => lia : core.
#[local]Hint Extern 10 (_ < _)%nat => lia : core.
#[local]Hint Extern 10 (_ <= _) => lia : core.
#[local]Hint Extern 10 (_ <= _)%nat => lia : core.
#[local]Hint Extern 10 (_ > _) => lia : core.
#[local]Hint Extern 10 (_ > _)%nat => lia : core.
#[local]Hint Extern 10 (_ >= _) => lia : core. 
#[local]Hint Extern 10 (_ >= _)%nat => lia : core. 
#[local]Hint Extern 10 (S _ = S _) => f_equal : core. 

Ltac extract v := match goal with
   | [ H: context[v = ?u] |- context[v] ] =>
      let H := fresh "H" in
      assert (H: v = u) by intuit; subst v
end.


Lemma BigLessThan_obligation0_trivial: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (v : Z), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x1 => ((^ x1) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x2 => ((^ x2) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x3 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x4 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> True -> ((v = 0%nat) -> True).
Proof. intuit. Qed.

Lemma BigLessThan_obligation1_trivial: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (v : Z), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x5 => ((^ x5) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x6 => ((^ x6) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x7 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x8 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> True -> (((v = k) /\ True) -> True).
Proof. intuit. Qed.

Lemma BigLessThan_obligation2: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (v : Z), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x9 => ((^ x9) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x10 => ((^ x10) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x11 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x12 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> True -> (((0%nat <= v) /\ (v < k)) -> (0%nat <= v)).
Proof. lia. Qed. 

Lemma BigLessThan_obligation3_trivial: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (i : nat) (v : F), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x13 => ((^ x13) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x14 => ((^ x14) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x15 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x16 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> (i < k) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((as_be n (xs'[:i])) < (as_be n (ys'[:i])))) /\ ((v = 0%F) -> ~((as_be n (xs'[:i])) < (as_be n (ys'[:i])))))) -> True).
Proof. intuit. Qed.

Lemma BigLessThan_obligation4_trivial: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (i : nat) (v : F), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x17 => ((^ x17) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x18 => ((^ x18) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x19 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x20 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> (i < k) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((as_be n (xs'[:i])) = (as_be n (ys'[:i])))) /\ ((v = 0%F) -> ~((as_be n (xs'[:i])) = (as_be n (ys'[:i])))))) -> True).
Proof. intuit. Qed.

Lemma BigLessThan_obligation5: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (i : nat) (lt_eq : (F * F)) (eq : F) (lt : F) (_u0 : (F * F)) (x : F) (y : F) (v : Z), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x21 => ((^ x21) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x22 => ((^ x22) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x23 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x24 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> (i < k) -> match lt_eq with (x25,x26) => (((x25 = 0%F) \/ (x25 = 1%F)) /\ (((x25 = 1%F) -> ((as_be n (xs'[:i])) < (as_be n (ys'[:i])))) /\ ((x25 = 0%F) -> ~((as_be n (xs'[:i])) < (as_be n (ys'[:i])))))) end -> match lt_eq with (x25,x26) => (((x26 = 0%F) \/ (x26 = 1%F)) /\ (((x26 = 1%F) -> ((as_be n (xs'[:i])) = (as_be n (ys'[:i])))) /\ ((x26 = 0%F) -> ~((as_be n (xs'[:i])) = (as_be n (ys'[:i])))))) end -> match lt_eq with (x25,x26) => True end -> (eq = (snd lt_eq)) -> (lt = (fst lt_eq)) -> match _u0 with (x27,x28) => True end -> match _u0 with (x27,x28) => True end -> match _u0 with (x27,x28) => ((lt_eq = lt_eq) /\ True) end -> (x = (xs'!i)) -> (y = (ys'!i)) -> True -> (((v = n) /\ True) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof. lia. Qed. 

Lemma BigLessThan_obligation6: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (i : nat) (lt_eq : (F * F)) (eq : F) (lt : F) (_u0 : (F * F)) (x : F) (y : F) (v : F), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x29 => ((^ x29) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x30 => ((^ x30) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x31 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x32 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> (i < k) -> match lt_eq with (x33,x34) => (((x33 = 0%F) \/ (x33 = 1%F)) /\ (((x33 = 1%F) -> ((as_be n (xs'[:i])) < (as_be n (ys'[:i])))) /\ ((x33 = 0%F) -> ~((as_be n (xs'[:i])) < (as_be n (ys'[:i])))))) end -> match lt_eq with (x33,x34) => (((x34 = 0%F) \/ (x34 = 1%F)) /\ (((x34 = 1%F) -> ((as_be n (xs'[:i])) = (as_be n (ys'[:i])))) /\ ((x34 = 0%F) -> ~((as_be n (xs'[:i])) = (as_be n (ys'[:i])))))) end -> match lt_eq with (x33,x34) => True end -> (eq = (snd lt_eq)) -> (lt = (fst lt_eq)) -> match _u0 with (x35,x36) => True end -> match _u0 with (x35,x36) => True end -> match _u0 with (x35,x36) => ((lt_eq = lt_eq) /\ True) end -> (x = (xs'!i)) -> (y = (ys'!i)) -> True -> (((v = x) /\ True) -> ((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z)).
Proof. intuit; subst; auto. Qed.

Lemma BigLessThan_obligation7: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (i : nat) (lt_eq : (F * F)) (eq : F) (lt : F) (_u0 : (F * F)) (x : F) (y : F) (v : F), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x37 => ((^ x37) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x38 => ((^ x38) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x39 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x40 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> (i < k) -> match lt_eq with (x41,x42) => (((x41 = 0%F) \/ (x41 = 1%F)) /\ (((x41 = 1%F) -> ((as_be n (xs'[:i])) < (as_be n (ys'[:i])))) /\ ((x41 = 0%F) -> ~((as_be n (xs'[:i])) < (as_be n (ys'[:i])))))) end -> match lt_eq with (x41,x42) => (((x42 = 0%F) \/ (x42 = 1%F)) /\ (((x42 = 1%F) -> ((as_be n (xs'[:i])) = (as_be n (ys'[:i])))) /\ ((x42 = 0%F) -> ~((as_be n (xs'[:i])) = (as_be n (ys'[:i])))))) end -> match lt_eq with (x41,x42) => True end -> (eq = (snd lt_eq)) -> (lt = (fst lt_eq)) -> match _u0 with (x43,x44) => True end -> match _u0 with (x43,x44) => True end -> match _u0 with (x43,x44) => ((lt_eq = lt_eq) /\ True) end -> (x = (xs'!i)) -> (y = (ys'!i)) -> True -> (((v = y) /\ True) -> ((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z)).
Proof. intuit; subst; auto. Qed.

Lemma BigLessThan_obligation8: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (i : nat) (lt_eq : (F * F)) (eq : F) (lt : F) (_u0 : (F * F)) (x : F) (y : F) (x_lt_y : F) (v : F), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x45 => ((^ x45) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x46 => ((^ x46) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x47 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x48 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> (i < k) -> match lt_eq with (x49,x50) => (((x49 = 0%F) \/ (x49 = 1%F)) /\ (((x49 = 1%F) -> ((as_be n (xs'[:i])) < (as_be n (ys'[:i])))) /\ ((x49 = 0%F) -> ~((as_be n (xs'[:i])) < (as_be n (ys'[:i])))))) end -> match lt_eq with (x49,x50) => (((x50 = 0%F) \/ (x50 = 1%F)) /\ (((x50 = 1%F) -> ((as_be n (xs'[:i])) = (as_be n (ys'[:i])))) /\ ((x50 = 0%F) -> ~((as_be n (xs'[:i])) = (as_be n (ys'[:i])))))) end -> match lt_eq with (x49,x50) => True end -> (eq = (snd lt_eq)) -> (lt = (fst lt_eq)) -> match _u0 with (x51,x52) => True end -> match _u0 with (x51,x52) => True end -> match _u0 with (x51,x52) => ((lt_eq = lt_eq) /\ True) end -> (x = (xs'!i)) -> (y = (ys'!i)) -> (((x_lt_y = 0%F) \/ (x_lt_y = 1%F)) /\ (((x_lt_y = 1%F) -> ((^ x) < (^ y))) /\ ((x_lt_y = 0%F) -> ~((^ x) < (^ y))))) -> True -> (((v = eq) /\ True) -> ((v = 0%F) \/ (v = 1%F))).
Proof. intuit; subst; auto. Qed.

Lemma BigLessThan_obligation9: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (i : nat) (lt_eq : (F * F)) (eq : F) (lt : F) (_u0 : (F * F)) (x : F) (y : F) (x_lt_y : F) (v : F), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x53 => ((^ x53) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x54 => ((^ x54) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x55 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x56 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> (i < k) -> match lt_eq with (x57,x58) => (((x57 = 0%F) \/ (x57 = 1%F)) /\ (((x57 = 1%F) -> ((as_be n (xs'[:i])) < (as_be n (ys'[:i])))) /\ ((x57 = 0%F) -> ~((as_be n (xs'[:i])) < (as_be n (ys'[:i])))))) end -> match lt_eq with (x57,x58) => (((x58 = 0%F) \/ (x58 = 1%F)) /\ (((x58 = 1%F) -> ((as_be n (xs'[:i])) = (as_be n (ys'[:i])))) /\ ((x58 = 0%F) -> ~((as_be n (xs'[:i])) = (as_be n (ys'[:i])))))) end -> match lt_eq with (x57,x58) => True end -> (eq = (snd lt_eq)) -> (lt = (fst lt_eq)) -> match _u0 with (x59,x60) => True end -> match _u0 with (x59,x60) => True end -> match _u0 with (x59,x60) => ((lt_eq = lt_eq) /\ True) end -> (x = (xs'!i)) -> (y = (ys'!i)) -> (((x_lt_y = 0%F) \/ (x_lt_y = 1%F)) /\ (((x_lt_y = 1%F) -> ((^ x) < (^ y))) /\ ((x_lt_y = 0%F) -> ~((^ x) < (^ y))))) -> True -> (((v = x_lt_y) /\ True) -> ((v = 0%F) \/ (v = 1%F))).
Proof. intuit; subst; auto. Qed.

Lemma BigLessThan_obligation10_trivial: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (i : nat) (lt_eq : (F * F)) (eq : F) (lt : F) (_u0 : (F * F)) (x : F) (y : F) (x_lt_y : F) (xs_lt_ys : F) (v : F), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x61 => ((^ x61) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x62 => ((^ x62) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x63 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x64 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> (i < k) -> match lt_eq with (x65,x66) => (((x65 = 0%F) \/ (x65 = 1%F)) /\ (((x65 = 1%F) -> ((as_be n (xs'[:i])) < (as_be n (ys'[:i])))) /\ ((x65 = 0%F) -> ~((as_be n (xs'[:i])) < (as_be n (ys'[:i])))))) end -> match lt_eq with (x65,x66) => (((x66 = 0%F) \/ (x66 = 1%F)) /\ (((x66 = 1%F) -> ((as_be n (xs'[:i])) = (as_be n (ys'[:i])))) /\ ((x66 = 0%F) -> ~((as_be n (xs'[:i])) = (as_be n (ys'[:i])))))) end -> match lt_eq with (x65,x66) => True end -> (eq = (snd lt_eq)) -> (lt = (fst lt_eq)) -> match _u0 with (x67,x68) => True end -> match _u0 with (x67,x68) => True end -> match _u0 with (x67,x68) => ((lt_eq = lt_eq) /\ True) end -> (x = (xs'!i)) -> (y = (ys'!i)) -> (((x_lt_y = 0%F) \/ (x_lt_y = 1%F)) /\ (((x_lt_y = 1%F) -> ((^ x) < (^ y))) /\ ((x_lt_y = 0%F) -> ~((^ x) < (^ y))))) -> (((xs_lt_ys = 0%F) \/ (xs_lt_ys = 1%F)) /\ (((xs_lt_ys = 1%F) -> (f_and eq x_lt_y)) /\ ((xs_lt_ys = 0%F) -> ~(f_and eq x_lt_y)))) -> True -> (((v = x) /\ True) -> True).
Proof. intuit. Qed.

Lemma BigLessThan_obligation11_trivial: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (i : nat) (lt_eq : (F * F)) (eq : F) (lt : F) (_u0 : (F * F)) (x : F) (y : F) (x_lt_y : F) (xs_lt_ys : F) (v : F), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x69 => ((^ x69) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x70 => ((^ x70) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x71 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x72 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> (i < k) -> match lt_eq with (x73,x74) => (((x73 = 0%F) \/ (x73 = 1%F)) /\ (((x73 = 1%F) -> ((as_be n (xs'[:i])) < (as_be n (ys'[:i])))) /\ ((x73 = 0%F) -> ~((as_be n (xs'[:i])) < (as_be n (ys'[:i])))))) end -> match lt_eq with (x73,x74) => (((x74 = 0%F) \/ (x74 = 1%F)) /\ (((x74 = 1%F) -> ((as_be n (xs'[:i])) = (as_be n (ys'[:i])))) /\ ((x74 = 0%F) -> ~((as_be n (xs'[:i])) = (as_be n (ys'[:i])))))) end -> match lt_eq with (x73,x74) => True end -> (eq = (snd lt_eq)) -> (lt = (fst lt_eq)) -> match _u0 with (x75,x76) => True end -> match _u0 with (x75,x76) => True end -> match _u0 with (x75,x76) => ((lt_eq = lt_eq) /\ True) end -> (x = (xs'!i)) -> (y = (ys'!i)) -> (((x_lt_y = 0%F) \/ (x_lt_y = 1%F)) /\ (((x_lt_y = 1%F) -> ((^ x) < (^ y))) /\ ((x_lt_y = 0%F) -> ~((^ x) < (^ y))))) -> (((xs_lt_ys = 0%F) \/ (xs_lt_ys = 1%F)) /\ (((xs_lt_ys = 1%F) -> (f_and eq x_lt_y)) /\ ((xs_lt_ys = 0%F) -> ~(f_and eq x_lt_y)))) -> True -> (((v = y) /\ True) -> True).
Proof. intuit. Qed.

Lemma BigLessThan_obligation12: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (i : nat) (lt_eq : (F * F)) (eq : F) (lt : F) (_u0 : (F * F)) (x : F) (y : F) (x_lt_y : F) (xs_lt_ys : F) (x_eq_y : F) (v : F), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x77 => ((^ x77) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x78 => ((^ x78) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x79 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x80 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> (i < k) -> match lt_eq with (x81,x82) => (((x81 = 0%F) \/ (x81 = 1%F)) /\ (((x81 = 1%F) -> ((as_be n (xs'[:i])) < (as_be n (ys'[:i])))) /\ ((x81 = 0%F) -> ~((as_be n (xs'[:i])) < (as_be n (ys'[:i])))))) end -> match lt_eq with (x81,x82) => (((x82 = 0%F) \/ (x82 = 1%F)) /\ (((x82 = 1%F) -> ((as_be n (xs'[:i])) = (as_be n (ys'[:i])))) /\ ((x82 = 0%F) -> ~((as_be n (xs'[:i])) = (as_be n (ys'[:i])))))) end -> match lt_eq with (x81,x82) => True end -> (eq = (snd lt_eq)) -> (lt = (fst lt_eq)) -> match _u0 with (x83,x84) => True end -> match _u0 with (x83,x84) => True end -> match _u0 with (x83,x84) => ((lt_eq = lt_eq) /\ True) end -> (x = (xs'!i)) -> (y = (ys'!i)) -> (((x_lt_y = 0%F) \/ (x_lt_y = 1%F)) /\ (((x_lt_y = 1%F) -> ((^ x) < (^ y))) /\ ((x_lt_y = 0%F) -> ~((^ x) < (^ y))))) -> (((xs_lt_ys = 0%F) \/ (xs_lt_ys = 1%F)) /\ (((xs_lt_ys = 1%F) -> (f_and eq x_lt_y)) /\ ((xs_lt_ys = 0%F) -> ~(f_and eq x_lt_y)))) -> (((x_eq_y = 0%F) \/ (x_eq_y = 1%F)) /\ (((x_eq_y = 1%F) -> (x = y)) /\ ((x_eq_y = 0%F) -> ~(x = y)))) -> True -> (((v = lt) /\ True) -> ((v = 0%F) \/ (v = 1%F))).
Proof. intuit; subst; auto. Qed.

Lemma BigLessThan_obligation13: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (i : nat) (lt_eq : (F * F)) (eq : F) (lt : F) (_u0 : (F * F)) (x : F) (y : F) (x_lt_y : F) (xs_lt_ys : F) (x_eq_y : F) (v : F), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x85 => ((^ x85) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x86 => ((^ x86) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x87 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x88 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> (i < k) -> match lt_eq with (x89,x90) => (((x89 = 0%F) \/ (x89 = 1%F)) /\ (((x89 = 1%F) -> ((as_be n (xs'[:i])) < (as_be n (ys'[:i])))) /\ ((x89 = 0%F) -> ~((as_be n (xs'[:i])) < (as_be n (ys'[:i])))))) end -> match lt_eq with (x89,x90) => (((x90 = 0%F) \/ (x90 = 1%F)) /\ (((x90 = 1%F) -> ((as_be n (xs'[:i])) = (as_be n (ys'[:i])))) /\ ((x90 = 0%F) -> ~((as_be n (xs'[:i])) = (as_be n (ys'[:i])))))) end -> match lt_eq with (x89,x90) => True end -> (eq = (snd lt_eq)) -> (lt = (fst lt_eq)) -> match _u0 with (x91,x92) => True end -> match _u0 with (x91,x92) => True end -> match _u0 with (x91,x92) => ((lt_eq = lt_eq) /\ True) end -> (x = (xs'!i)) -> (y = (ys'!i)) -> (((x_lt_y = 0%F) \/ (x_lt_y = 1%F)) /\ (((x_lt_y = 1%F) -> ((^ x) < (^ y))) /\ ((x_lt_y = 0%F) -> ~((^ x) < (^ y))))) -> (((xs_lt_ys = 0%F) \/ (xs_lt_ys = 1%F)) /\ (((xs_lt_ys = 1%F) -> (f_and eq x_lt_y)) /\ ((xs_lt_ys = 0%F) -> ~(f_and eq x_lt_y)))) -> (((x_eq_y = 0%F) \/ (x_eq_y = 1%F)) /\ (((x_eq_y = 1%F) -> (x = y)) /\ ((x_eq_y = 0%F) -> ~(x = y)))) -> True -> (((v = xs_lt_ys) /\ True) -> ((v = 0%F) \/ (v = 1%F))).
Proof. intuit; subst; auto. Qed.

Lemma BigLessThan_obligation14: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (i : nat) (lt_eq : (F * F)) (eq : F) (lt : F) (_u0 : (F * F)) (x : F) (y : F) (x_lt_y : F) (xs_lt_ys : F) (x_eq_y : F) (v : F), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x93 => ((^ x93) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x94 => ((^ x94) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x95 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x96 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> (i < k) -> match lt_eq with (x97,x98) => (((x97 = 0%F) \/ (x97 = 1%F)) /\ (((x97 = 1%F) -> ((as_be n (xs'[:i])) < (as_be n (ys'[:i])))) /\ ((x97 = 0%F) -> ~((as_be n (xs'[:i])) < (as_be n (ys'[:i])))))) end -> match lt_eq with (x97,x98) => (((x98 = 0%F) \/ (x98 = 1%F)) /\ (((x98 = 1%F) -> ((as_be n (xs'[:i])) = (as_be n (ys'[:i])))) /\ ((x98 = 0%F) -> ~((as_be n (xs'[:i])) = (as_be n (ys'[:i])))))) end -> match lt_eq with (x97,x98) => True end -> (eq = (snd lt_eq)) -> (lt = (fst lt_eq)) -> match _u0 with (x99,x100) => True end -> match _u0 with (x99,x100) => True end -> match _u0 with (x99,x100) => ((lt_eq = lt_eq) /\ True) end -> (x = (xs'!i)) -> (y = (ys'!i)) -> (((x_lt_y = 0%F) \/ (x_lt_y = 1%F)) /\ (((x_lt_y = 1%F) -> ((^ x) < (^ y))) /\ ((x_lt_y = 0%F) -> ~((^ x) < (^ y))))) -> (((xs_lt_ys = 0%F) \/ (xs_lt_ys = 1%F)) /\ (((xs_lt_ys = 1%F) -> (f_and eq x_lt_y)) /\ ((xs_lt_ys = 0%F) -> ~(f_and eq x_lt_y)))) -> (((x_eq_y = 0%F) \/ (x_eq_y = 1%F)) /\ (((x_eq_y = 1%F) -> (x = y)) /\ ((x_eq_y = 0%F) -> ~(x = y)))) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_or lt xs_lt_ys)) /\ ((v = 0%F) -> ~(f_or lt xs_lt_ys)))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((as_be n (xs'[:(i + 1%nat)%nat])) < (as_be n (ys'[:(i + 1%nat)%nat])))) /\ ((v = 0%F) -> ~((as_be n (xs'[:(i + 1%nat)%nat])) < (as_be n (ys'[:(i + 1%nat)%nat]))))))).
Proof. Admitted.

Lemma BigLessThan_obligation15: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (i : nat) (lt_eq : (F * F)) (eq : F) (lt : F) (_u0 : (F * F)) (x : F) (y : F) (x_lt_y : F) (xs_lt_ys : F) (x_eq_y : F) (v : F), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x101 => ((^ x101) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x102 => ((^ x102) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x103 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x104 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> (i < k) -> match lt_eq with (x105,x106) => (((x105 = 0%F) \/ (x105 = 1%F)) /\ (((x105 = 1%F) -> ((as_be n (xs'[:i])) < (as_be n (ys'[:i])))) /\ ((x105 = 0%F) -> ~((as_be n (xs'[:i])) < (as_be n (ys'[:i])))))) end -> match lt_eq with (x105,x106) => (((x106 = 0%F) \/ (x106 = 1%F)) /\ (((x106 = 1%F) -> ((as_be n (xs'[:i])) = (as_be n (ys'[:i])))) /\ ((x106 = 0%F) -> ~((as_be n (xs'[:i])) = (as_be n (ys'[:i])))))) end -> match lt_eq with (x105,x106) => True end -> (eq = (snd lt_eq)) -> (lt = (fst lt_eq)) -> match _u0 with (x107,x108) => True end -> match _u0 with (x107,x108) => True end -> match _u0 with (x107,x108) => ((lt_eq = lt_eq) /\ True) end -> (x = (xs'!i)) -> (y = (ys'!i)) -> (((x_lt_y = 0%F) \/ (x_lt_y = 1%F)) /\ (((x_lt_y = 1%F) -> ((^ x) < (^ y))) /\ ((x_lt_y = 0%F) -> ~((^ x) < (^ y))))) -> (((xs_lt_ys = 0%F) \/ (xs_lt_ys = 1%F)) /\ (((xs_lt_ys = 1%F) -> (f_and eq x_lt_y)) /\ ((xs_lt_ys = 0%F) -> ~(f_and eq x_lt_y)))) -> (((x_eq_y = 0%F) \/ (x_eq_y = 1%F)) /\ (((x_eq_y = 1%F) -> (x = y)) /\ ((x_eq_y = 0%F) -> ~(x = y)))) -> True -> (((v = eq) /\ True) -> ((v = 0%F) \/ (v = 1%F))).
Proof. intuit; subst; auto. Qed.

Lemma BigLessThan_obligation16: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (i : nat) (lt_eq : (F * F)) (eq : F) (lt : F) (_u0 : (F * F)) (x : F) (y : F) (x_lt_y : F) (xs_lt_ys : F) (x_eq_y : F) (v : F), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x109 => ((^ x109) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x110 => ((^ x110) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x111 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x112 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> (i < k) -> match lt_eq with (x113,x114) => (((x113 = 0%F) \/ (x113 = 1%F)) /\ (((x113 = 1%F) -> ((as_be n (xs'[:i])) < (as_be n (ys'[:i])))) /\ ((x113 = 0%F) -> ~((as_be n (xs'[:i])) < (as_be n (ys'[:i])))))) end -> match lt_eq with (x113,x114) => (((x114 = 0%F) \/ (x114 = 1%F)) /\ (((x114 = 1%F) -> ((as_be n (xs'[:i])) = (as_be n (ys'[:i])))) /\ ((x114 = 0%F) -> ~((as_be n (xs'[:i])) = (as_be n (ys'[:i])))))) end -> match lt_eq with (x113,x114) => True end -> (eq = (snd lt_eq)) -> (lt = (fst lt_eq)) -> match _u0 with (x115,x116) => True end -> match _u0 with (x115,x116) => True end -> match _u0 with (x115,x116) => ((lt_eq = lt_eq) /\ True) end -> (x = (xs'!i)) -> (y = (ys'!i)) -> (((x_lt_y = 0%F) \/ (x_lt_y = 1%F)) /\ (((x_lt_y = 1%F) -> ((^ x) < (^ y))) /\ ((x_lt_y = 0%F) -> ~((^ x) < (^ y))))) -> (((xs_lt_ys = 0%F) \/ (xs_lt_ys = 1%F)) /\ (((xs_lt_ys = 1%F) -> (f_and eq x_lt_y)) /\ ((xs_lt_ys = 0%F) -> ~(f_and eq x_lt_y)))) -> (((x_eq_y = 0%F) \/ (x_eq_y = 1%F)) /\ (((x_eq_y = 1%F) -> (x = y)) /\ ((x_eq_y = 0%F) -> ~(x = y)))) -> True -> (((v = x_eq_y) /\ True) -> ((v = 0%F) \/ (v = 1%F))).
Proof. intuit; subst; auto. Qed.

Lemma BigLessThan_obligation17: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (i : nat) (lt_eq : (F * F)) (eq : F) (lt : F) (_u0 : (F * F)) (x : F) (y : F) (x_lt_y : F) (xs_lt_ys : F) (x_eq_y : F) (v : F), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x117 => ((^ x117) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x118 => ((^ x118) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x119 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x120 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> (i < k) -> match lt_eq with (x121,x122) => (((x121 = 0%F) \/ (x121 = 1%F)) /\ (((x121 = 1%F) -> ((as_be n (xs'[:i])) < (as_be n (ys'[:i])))) /\ ((x121 = 0%F) -> ~((as_be n (xs'[:i])) < (as_be n (ys'[:i])))))) end -> match lt_eq with (x121,x122) => (((x122 = 0%F) \/ (x122 = 1%F)) /\ (((x122 = 1%F) -> ((as_be n (xs'[:i])) = (as_be n (ys'[:i])))) /\ ((x122 = 0%F) -> ~((as_be n (xs'[:i])) = (as_be n (ys'[:i])))))) end -> match lt_eq with (x121,x122) => True end -> (eq = (snd lt_eq)) -> (lt = (fst lt_eq)) -> match _u0 with (x123,x124) => True end -> match _u0 with (x123,x124) => True end -> match _u0 with (x123,x124) => ((lt_eq = lt_eq) /\ True) end -> (x = (xs'!i)) -> (y = (ys'!i)) -> (((x_lt_y = 0%F) \/ (x_lt_y = 1%F)) /\ (((x_lt_y = 1%F) -> ((^ x) < (^ y))) /\ ((x_lt_y = 0%F) -> ~((^ x) < (^ y))))) -> (((xs_lt_ys = 0%F) \/ (xs_lt_ys = 1%F)) /\ (((xs_lt_ys = 1%F) -> (f_and eq x_lt_y)) /\ ((xs_lt_ys = 0%F) -> ~(f_and eq x_lt_y)))) -> (((x_eq_y = 0%F) \/ (x_eq_y = 1%F)) /\ (((x_eq_y = 1%F) -> (x = y)) /\ ((x_eq_y = 0%F) -> ~(x = y)))) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (f_and eq x_eq_y)) /\ ((v = 0%F) -> ~(f_and eq x_eq_y)))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((as_be n (xs'[:(i + 1%nat)%nat])) = (as_be n (ys'[:(i + 1%nat)%nat])))) /\ ((v = 0%F) -> ~((as_be n (xs'[:(i + 1%nat)%nat])) = (as_be n (ys'[:(i + 1%nat)%nat]))))))).
Proof. 
   intros. unfold f_or, f_and, as_le, as_be in *.
   destruct lt_eq as [_lt _eq]. simpl in *. subst _lt _eq.
   (* repeat rewrite firstn_plus1 by lia. *)
   (* repeat rewrite RZ.as_be_app. *)
   split. intuit.
   split; intro;
   ind v; subst x y; simpl; unfold RZ.ToZ.to_Z; simplify.
   - 
   destruct H13. ind eq. ind x_eq_y. 
   rewrite big_eq_step. 
   apply f_equal with (f:=F.to_Z) in H14. auto.
   - destruct (dec (eq = 1%F)).
   + 
      ind eq.
      assert (x_eq_y <> 1%F). intro. auto.
      ind x_eq_y.
      intro. rewrite big_eq_step in H14.  destruct H14. apply H11. 
      apply RZU.F_to_Z_inj. auto.
   + ind eq. 
      intro. rewrite big_eq_step in H11.  destruct H11. apply n0. auto.
Qed.

Lemma BigLessThan_obligation18_trivial: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (i : nat) (lt_eq : (F * F)) (eq : F) (lt : F) (_u0 : (F * F)) (x : F) (y : F) (x_lt_y : F) (xs_lt_ys : F) (x_eq_y : F), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x125 => ((^ x125) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x126 => ((^ x126) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x127 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x128 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> (i < k) -> match lt_eq with (x129,x130) => (((x129 = 0%F) \/ (x129 = 1%F)) /\ (((x129 = 1%F) -> ((as_be n (xs'[:i])) < (as_be n (ys'[:i])))) /\ ((x129 = 0%F) -> ~((as_be n (xs'[:i])) < (as_be n (ys'[:i])))))) end -> match lt_eq with (x129,x130) => (((x130 = 0%F) \/ (x130 = 1%F)) /\ (((x130 = 1%F) -> ((as_be n (xs'[:i])) = (as_be n (ys'[:i])))) /\ ((x130 = 0%F) -> ~((as_be n (xs'[:i])) = (as_be n (ys'[:i])))))) end -> match lt_eq with (x129,x130) => True end -> (eq = (snd lt_eq)) -> (lt = (fst lt_eq)) -> match _u0 with (x131,x132) => True end -> match _u0 with (x131,x132) => True end -> match _u0 with (x131,x132) => ((lt_eq = lt_eq) /\ True) end -> (x = (xs'!i)) -> (y = (ys'!i)) -> (((x_lt_y = 0%F) \/ (x_lt_y = 1%F)) /\ (((x_lt_y = 1%F) -> ((^ x) < (^ y))) /\ ((x_lt_y = 0%F) -> ~((^ x) < (^ y))))) -> (((xs_lt_ys = 0%F) \/ (xs_lt_ys = 1%F)) /\ (((xs_lt_ys = 1%F) -> (f_and eq x_lt_y)) /\ ((xs_lt_ys = 0%F) -> ~(f_and eq x_lt_y)))) -> (((x_eq_y = 0%F) \/ (x_eq_y = 1%F)) /\ (((x_eq_y = 1%F) -> (x = y)) /\ ((x_eq_y = 0%F) -> ~(x = y)))) -> (True -> True).
Proof. intuit. Qed.

Lemma BigLessThan_obligation19: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (v : F), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x133 => ((^ x133) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x134 => ((^ x134) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x135 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x136 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> True -> ((v = 0%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((as_be n (xs'[:0%nat])) < (as_be n (ys'[:0%nat])))) /\ ((v = 0%F) -> ~((as_be n (xs'[:0%nat])) < (as_be n (ys'[:0%nat]))))))).
Proof. unwrap_C. simpl. intuit. exfalso. fqsatz. lia. Qed.

Lemma BigLessThan_obligation20: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (v : F), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x137 => ((^ x137) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x138 => ((^ x138) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x139 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x140 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> True -> ((v = 1%F) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((as_be n (xs'[:0%nat])) = (as_be n (ys'[:0%nat])))) /\ ((v = 0%F) -> ~((as_be n (xs'[:0%nat])) = (as_be n (ys'[:0%nat]))))))).
Proof. unwrap_C. simpl. intuit. exfalso. fqsatz.  Qed.


Lemma BigLessThan_obligation21_trivial: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x141 => ((^ x141) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x142 => ((^ x142) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x143 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x144 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> (True -> True).
Proof. intuit. Qed.

Lemma BigLessThan_obligation22: forall (n : nat) (k : nat) (xs : (list F)) (ys : (list F)) (xs' : (list F)) (ys' : (list F)) (v : F), (n <= (C.k - 1%nat)%Z) -> (2%nat <= k) -> Forall (fun x145 => ((^ x145) <= ((2%nat ^ n)%Z - 1%nat)%Z)) xs -> ((length xs) = k) -> Forall (fun x146 => ((^ x146) <= ((2%nat ^ n)%Z - 1%nat)%Z)) ys -> ((length ys) = k) -> Forall (fun x147 => True) xs' -> ((xs' = (rev xs)) /\ ((length xs') = (length xs))) -> Forall (fun x148 => True) ys' -> ((ys' = (rev ys)) /\ ((length ys') = (length ys))) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((as_be n (xs'[:k])) < (as_be n (ys'[:k])))) /\ ((v = 0%F) -> ~((as_be n (xs'[:k])) < (as_be n (ys'[:k])))))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((as_le n xs) < (as_le n ys))) /\ ((v = 0%F) -> ~((as_le n xs) < (as_le n ys)))))).
Proof.
   unfold as_be, as_le.
   intuit; 
   repeat rewrite firstn_all2 in * by lia;
   repeat rewrite RZ.be__rev_le in *;
   subst xs' ys';
   repeat rewrite rev_involutive in *;
   lia.
Qed.