(** * DSL benchmark: CircomRLN *)

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

From Circom Require Import Circom Util Default Tuple ListUtil LibTactics Simplify Repr Coda.
From Circom.CircomLib Require Import Bitify.

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope Z_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Definition Poseidon (nInputs : nat) (inputs : list F) : F. Admitted.

Axiom Poseidon_2 : forall inputs : list F,
  length inputs = 2%nat ->
  Poseidon 2%nat inputs = Poseidon 2%nat ((inputs!0%nat)::(inputs!1%nat)::nil).

Axiom k_rng: k > 252.

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

Definition zip {A B} (xs : list A) (ys : list B) := combine xs ys.

(* Note: This is a placeholder implementation that lets us prove many
trivial and even some nontrivial MerkleTreeInclusionProof obligations *)
Definition MrklTreeInclPfHash (xs : list (F * F)) (init : F) := 
  fold_left (fun (y:F) (x:(F*F)) => if dec (fst x = 0%F) then (Poseidon 2%nat (y :: (snd x) :: nil)) else (Poseidon 2%nat ((snd x):: y :: nil))) 
                       xs init.


(* MerkleTreeInclusionProof *)

Lemma MerkleTreeInclusionProof_obligation0_trivial: forall (DEPTH : nat) (leaf : F) (pathIndex : (list F)) (pathElements : (list F)) (z : (list (F * F))) (v : Z), True -> Forall (fun x0 => True) pathIndex -> ((length pathIndex) = DEPTH) -> Forall (fun x1 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x4 => match x4 with (x2,x3) => True end) z -> Forall (fun x4 => match x4 with (x2,x3) => True end) z -> Forall (fun x4 => match x4 with (x2,x3) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndex) -> (((fst (z!iz)) = (pathIndex!iz)) /\ ((snd (z!iz)) = (pathElements!iz)))) /\ ((length z) = (length pathIndex))) -> True -> ((v = 0%nat) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation1_trivial: forall (DEPTH : nat) (leaf : F) (pathIndex : (list F)) (pathElements : (list F)) (z : (list (F * F))) (v : Z), True -> Forall (fun x5 => True) pathIndex -> ((length pathIndex) = DEPTH) -> Forall (fun x6 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x9 => match x9 with (x7,x8) => True end) z -> Forall (fun x9 => match x9 with (x7,x8) => True end) z -> Forall (fun x9 => match x9 with (x7,x8) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndex) -> (((fst (z!iz)) = (pathIndex!iz)) /\ ((snd (z!iz)) = (pathElements!iz)))) /\ ((length z) = (length pathIndex))) -> True -> (((0%nat <= v) /\ (v = DEPTH)) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation2_trivial: forall (DEPTH : nat) (leaf : F) (pathIndex : (list F)) (pathElements : (list F)) (z : (list (F * F))) (v : Z), True -> Forall (fun x10 => True) pathIndex -> ((length pathIndex) = DEPTH) -> Forall (fun x11 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x14 => match x14 with (x12,x13) => True end) z -> Forall (fun x14 => match x14 with (x12,x13) => True end) z -> Forall (fun x14 => match x14 with (x12,x13) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndex) -> (((fst (z!iz)) = (pathIndex!iz)) /\ ((snd (z!iz)) = (pathElements!iz)))) /\ ((length z) = (length pathIndex))) -> True -> (((0%nat <= v) /\ (v < DEPTH)) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation3_trivial: forall (DEPTH : nat) (leaf : F) (pathIndex : (list F)) (pathElements : (list F)) (z : (list (F * F))) (_i : nat) (v : F), True -> Forall (fun x15 => True) pathIndex -> ((length pathIndex) = DEPTH) -> Forall (fun x16 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x19 => match x19 with (x17,x18) => True end) z -> Forall (fun x19 => match x19 with (x17,x18) => True end) z -> Forall (fun x19 => match x19 with (x17,x18) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndex) -> (((fst (z!iz)) = (pathIndex!iz)) /\ ((snd (z!iz)) = (pathElements!iz)))) /\ ((length z) = (length pathIndex))) -> (_i < DEPTH) -> True -> ((v = (MrklTreeInclPfHash (take _i z) leaf)) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation4_trivial: forall (DEPTH : nat) (leaf : F) (pathIndex : (list F)) (pathElements : (list F)) (z : (list (F * F))) (_i : nat) (x : F) (v : F), True -> Forall (fun x20 => True) pathIndex -> ((length pathIndex) = DEPTH) -> Forall (fun x21 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x24 => match x24 with (x22,x23) => True end) z -> Forall (fun x24 => match x24 with (x22,x23) => True end) z -> Forall (fun x24 => match x24 with (x22,x23) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndex) -> (((fst (z!iz)) = (pathIndex!iz)) /\ ((snd (z!iz)) = (pathElements!iz)))) /\ ((length z) = (length pathIndex))) -> (_i < DEPTH) -> (x = (MrklTreeInclPfHash (take _i z) leaf)) -> True -> ((v = 1%F) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation5_trivial: forall (DEPTH : nat) (leaf : F) (pathIndex : (list F)) (pathElements : (list F)) (z : (list (F * F))) (_i : nat) (x : F) (v : F), True -> Forall (fun x25 => True) pathIndex -> ((length pathIndex) = DEPTH) -> Forall (fun x26 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x29 => match x29 with (x27,x28) => True end) z -> Forall (fun x29 => match x29 with (x27,x28) => True end) z -> Forall (fun x29 => match x29 with (x27,x28) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndex) -> (((fst (z!iz)) = (pathIndex!iz)) /\ ((snd (z!iz)) = (pathElements!iz)))) /\ ((length z) = (length pathIndex))) -> (_i < DEPTH) -> (x = (MrklTreeInclPfHash (take _i z) leaf)) -> True -> ((v = (1%F - (fst (z!_i)))%F) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation6: forall (DEPTH : nat) (leaf : F) (pathIndex : (list F)) (pathElements : (list F)) (z : (list (F * F))) (_i : nat) (x : F) (u0 : unit) (c : (list (list F))) (v : Z), True -> Forall (fun x30 => True) pathIndex -> ((length pathIndex) = DEPTH) -> Forall (fun x31 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x34 => match x34 with (x32,x33) => True end) z -> Forall (fun x34 => match x34 with (x32,x33) => True end) z -> Forall (fun x34 => match x34 with (x32,x33) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndex) -> (((fst (z!iz)) = (pathIndex!iz)) /\ ((snd (z!iz)) = (pathElements!iz)))) /\ ((length z) = (length pathIndex))) -> (_i < DEPTH) -> (x = (MrklTreeInclPfHash (take _i z) leaf)) -> (((fst (z!_i)) * (1%F - (fst (z!_i)))%F)%F = 0%F) -> Forall (fun x36 => Forall (fun x35 => True) x36) c -> Forall (fun x36 => ((length x36) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: ((snd (z!_i)) :: nil)))) /\ ((c!1%nat) = ((snd (z!_i)) :: (x :: nil)))) /\ ((length c) = 2%nat)) -> True -> ((v = 2%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation7: forall (DEPTH : nat) (leaf : F) (pathIndex : (list F)) (pathElements : (list F)) (z : (list (F * F))) (_i : nat) (x : F) (u0 : unit) (c : (list (list F))) (v : (list (list F))), True -> Forall (fun x37 => True) pathIndex -> ((length pathIndex) = DEPTH) -> Forall (fun x38 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x41 => match x41 with (x39,x40) => True end) z -> Forall (fun x41 => match x41 with (x39,x40) => True end) z -> Forall (fun x41 => match x41 with (x39,x40) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndex) -> (((fst (z!iz)) = (pathIndex!iz)) /\ ((snd (z!iz)) = (pathElements!iz)))) /\ ((length z) = (length pathIndex))) -> (_i < DEPTH) -> (x = (MrklTreeInclPfHash (take _i z) leaf)) -> (((fst (z!_i)) * (1%F - (fst (z!_i)))%F)%F = 0%F) -> Forall (fun x43 => Forall (fun x42 => True) x43) c -> Forall (fun x43 => ((length x43) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: ((snd (z!_i)) :: nil)))) /\ ((c!1%nat) = ((snd (z!_i)) :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x45 => Forall (fun x44 => True) x45) v -> Forall (fun x45 => ((length x45) = 2%nat)) v -> True -> (((((True /\ ((v!0%nat) = (x :: ((snd (z!_i)) :: nil)))) /\ ((v!1%nat) = ((snd (z!_i)) :: (x :: nil)))) /\ ((length v) = 2%nat)) /\ (v = c)) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation8: forall (DEPTH : nat) (leaf : F) (pathIndex : (list F)) (pathElements : (list F)) (z : (list (F * F))) (_i : nat) (x : F) (u0 : unit) (c : (list (list F))) (v : (list F)), True -> Forall (fun x46 => True) pathIndex -> ((length pathIndex) = DEPTH) -> Forall (fun x47 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x50 => match x50 with (x48,x49) => True end) z -> Forall (fun x50 => match x50 with (x48,x49) => True end) z -> Forall (fun x50 => match x50 with (x48,x49) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndex) -> (((fst (z!iz)) = (pathIndex!iz)) /\ ((snd (z!iz)) = (pathElements!iz)))) /\ ((length z) = (length pathIndex))) -> (_i < DEPTH) -> (x = (MrklTreeInclPfHash (take _i z) leaf)) -> (((fst (z!_i)) * (1%F - (fst (z!_i)))%F)%F = 0%F) -> Forall (fun x52 => Forall (fun x51 => True) x52) c -> Forall (fun x52 => ((length x52) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: ((snd (z!_i)) :: nil)))) /\ ((c!1%nat) = ((snd (z!_i)) :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x53 => True) v -> True -> (((length v) = 2%nat) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation9: forall (DEPTH : nat) (leaf : F) (pathIndex : (list F)) (pathElements : (list F)) (z : (list (F * F))) (_i : nat) (x : F) (u0 : unit) (c : (list (list F))) (m : (list F)) (v : Z), True -> Forall (fun x54 => True) pathIndex -> ((length pathIndex) = DEPTH) -> Forall (fun x55 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x58 => match x58 with (x56,x57) => True end) z -> Forall (fun x58 => match x58 with (x56,x57) => True end) z -> Forall (fun x58 => match x58 with (x56,x57) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndex) -> (((fst (z!iz)) = (pathIndex!iz)) /\ ((snd (z!iz)) = (pathElements!iz)))) /\ ((length z) = (length pathIndex))) -> (_i < DEPTH) -> (x = (MrklTreeInclPfHash (take _i z) leaf)) -> (((fst (z!_i)) * (1%F - (fst (z!_i)))%F)%F = 0%F) -> Forall (fun x60 => Forall (fun x59 => True) x60) c -> Forall (fun x60 => ((length x60) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: ((snd (z!_i)) :: nil)))) /\ ((c!1%nat) = ((snd (z!_i)) :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x61 => True) m -> ((forall (i:nat), 0%nat <= i < 2%nat -> ((m!i) = (((((c!i)!1%nat) - ((c!i)!0%nat))%F * (fst (z!_i)))%F + ((c!i)!0%nat))%F)) /\ ((length m) = 2%nat)) -> True -> ((v = 2%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation10: forall (DEPTH : nat) (leaf : F) (pathIndex : (list F)) (pathElements : (list F)) (z : (list (F * F))) (_i : nat) (x : F) (u0 : unit) (c : (list (list F))) (m : (list F)) (v : (list F)), True -> Forall (fun x62 => True) pathIndex -> ((length pathIndex) = DEPTH) -> Forall (fun x63 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x66 => match x66 with (x64,x65) => True end) z -> Forall (fun x66 => match x66 with (x64,x65) => True end) z -> Forall (fun x66 => match x66 with (x64,x65) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndex) -> (((fst (z!iz)) = (pathIndex!iz)) /\ ((snd (z!iz)) = (pathElements!iz)))) /\ ((length z) = (length pathIndex))) -> (_i < DEPTH) -> (x = (MrklTreeInclPfHash (take _i z) leaf)) -> (((fst (z!_i)) * (1%F - (fst (z!_i)))%F)%F = 0%F) -> Forall (fun x68 => Forall (fun x67 => True) x68) c -> Forall (fun x68 => ((length x68) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: ((snd (z!_i)) :: nil)))) /\ ((c!1%nat) = ((snd (z!_i)) :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x69 => True) m -> ((forall (i:nat), 0%nat <= i < 2%nat -> ((m!i) = (((((c!i)!1%nat) - ((c!i)!0%nat))%F * (fst (z!_i)))%F + ((c!i)!0%nat))%F)) /\ ((length m) = 2%nat)) -> Forall (fun x70 => True) v -> True -> ((((forall (i:nat), 0%nat <= i < 2%nat -> ((v!i) = (((((c!i)!1%nat) - ((c!i)!0%nat))%F * (fst (z!_i)))%F + ((c!i)!0%nat))%F)) /\ ((length v) = 2%nat)) /\ (v = m)) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation11: forall (DEPTH : nat) (leaf : F) (pathIndex : (list F)) (pathElements : (list F)) (z : (list (F * F))) (_i : nat) (x : F) (u0 : unit) (c : (list (list F))) (m : (list F)) (v : F), True -> Forall (fun x71 => True) pathIndex -> ((length pathIndex) = DEPTH) -> Forall (fun x72 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x75 => match x75 with (x73,x74) => True end) z -> Forall (fun x75 => match x75 with (x73,x74) => True end) z -> Forall (fun x75 => match x75 with (x73,x74) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndex) -> (((fst (z!iz)) = (pathIndex!iz)) /\ ((snd (z!iz)) = (pathElements!iz)))) /\ ((length z) = (length pathIndex))) -> (_i < DEPTH) -> (x = (MrklTreeInclPfHash (take _i z) leaf)) -> (((fst (z!_i)) * (1%F - (fst (z!_i)))%F)%F = 0%F) -> Forall (fun x77 => Forall (fun x76 => True) x77) c -> Forall (fun x77 => ((length x77) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: ((snd (z!_i)) :: nil)))) /\ ((c!1%nat) = ((snd (z!_i)) :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x78 => True) m -> ((forall (i:nat), 0%nat <= i < 2%nat -> ((m!i) = (((((c!i)!1%nat) - ((c!i)!0%nat))%F * (fst (z!_i)))%F + ((c!i)!0%nat))%F)) /\ ((length m) = 2%nat)) -> True -> ((v = (Poseidon 2%nat m)) -> (v = (MrklTreeInclPfHash (take (_i + 1%nat)%nat z) leaf))).
Proof. 
intuition; subst; unfold MrklTreeInclPfHash, take in *; simpl in *;unwrap_C.
specialize (H13 0%nat) as Hm1; specialize (H13 1%nat) as Hm2; simpl in *.
assert ((c!1)!0%nat = snd (z ! _i)). { rewrite H22. auto. } 
assert ((c!0)!1%nat = snd (z ! _i)). { rewrite H23. auto. }
assert ((c!1)!1%nat = fold_left (fun (y : F) (x : F * F) => if dec (fst x = 0)%F then Poseidon 2 (y :: snd x :: nil) else Poseidon 2 (snd x :: y :: nil)) (z [:_i]) leaf). 
{ rewrite H22. auto. }
assert ((c!0)!0%nat = fold_left (fun (y : F) (x : F * F) => if dec (fst x = 0)%F then Poseidon 2 (y :: snd x :: nil) else Poseidon 2 (snd x :: y :: nil)) (z [:_i]) leaf). 
{ rewrite H23. auto. }
rewrite Poseidon_2;auto. 
replace (_i + 1)%nat with (S _i) by lia. rewrite fold_left_firstn_S; auto.
destruct dec.
- rewrite e in *. 
  assert (m ! 1 = snd (z ! _i)). 
  { rewrite Hm2;auto. rewrite Fmul_0_r. rewrite Fadd_0_l. auto. }
  assert (m ! 0 = (c ! 0) ! 0).
  { rewrite Hm1;auto. rewrite Fmul_0_r. rewrite Fadd_0_l. auto. }
  rewrite H25, H24. rewrite H17. auto.
- assert (fst (z ! _i) = 1%F). { fqsatz. }
  rewrite H24 in *.
  assert (m ! 1 = (c ! 1) ! 1) by (rewrite Hm2;auto;try fqsatz).
  assert (m ! 0 = snd (z ! _i)) by (rewrite Hm1;auto;try fqsatz).
  rewrite H25, H26. rewrite H15. auto.
Qed.

Lemma MerkleTreeInclusionProof_obligation12: forall (DEPTH : nat) (leaf : F) (pathIndex : (list F)) (pathElements : (list F)) (z : (list (F * F))) (v : F), True -> Forall (fun x79 => True) pathIndex -> ((length pathIndex) = DEPTH) -> Forall (fun x80 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x83 => match x83 with (x81,x82) => True end) z -> Forall (fun x83 => match x83 with (x81,x82) => True end) z -> Forall (fun x83 => match x83 with (x81,x82) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndex) -> (((fst (z!iz)) = (pathIndex!iz)) /\ ((snd (z!iz)) = (pathElements!iz)))) /\ ((length z) = (length pathIndex))) -> True -> ((v = leaf) -> (v = (MrklTreeInclPfHash (take 0%nat z) leaf))).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation13: forall (DEPTH : nat) (leaf : F) (pathIndex : (list F)) (pathElements : (list F)) (z : (list (F * F))) (v : F), True -> Forall (fun x84 => True) pathIndex -> ((length pathIndex) = DEPTH) -> Forall (fun x85 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x88 => match x88 with (x86,x87) => True end) z -> Forall (fun x88 => match x88 with (x86,x87) => True end) z -> Forall (fun x88 => match x88 with (x86,x87) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length pathIndex) -> (((fst (z!iz)) = (pathIndex!iz)) /\ ((snd (z!iz)) = (pathElements!iz)))) /\ ((length z) = (length pathIndex))) -> True -> ((v = (MrklTreeInclPfHash (take DEPTH z) leaf)) -> (v = (MrklTreeInclPfHash (zip pathIndex pathElements) leaf))).
Proof. 
  intuition; unwrap_C.
  unfold zip, take in *; simpl in *.
  assert (z = combine pathIndex pathElements).
  { apply list_combine_eq_forall;auto. }
  rewrite <- H7. rewrite <- H1 in H9. rewrite <- H11 in H9.
  erewrite ListUtil.List.firstn_all in H9;auto.
Qed.



(* RangeCheck *)

Lemma RangeCheck_obligation0: forall (LIMIT_BIT_SIZE : nat) (messageId : F) (limit : F) (v : Z), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> ((((0%nat <= v) /\ ((v < 253%nat) /\ True)) /\ (v = LIMIT_BIT_SIZE)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma RangeCheck_obligation1_trivial: forall (LIMIT_BIT_SIZE : nat) (messageId : F) (limit : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> ((v = messageId) -> True).
Proof. hammer. Qed.

Lemma RangeCheck_obligation2: forall (LIMIT_BIT_SIZE : nat) (messageId : F) (limit : F) (bitCheck : (list F)) (v : Z), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x89 => ((x89 = 0%F) \/ (x89 = 1%F))) bitCheck -> (((as_le_f bitCheck) = messageId) /\ ((length bitCheck) = LIMIT_BIT_SIZE)) -> True -> ((((0%nat <= v) /\ ((v < 253%nat) /\ True)) /\ (v = LIMIT_BIT_SIZE)) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof. 
intros. intuition. pose proof k_rng. lia.
Qed.

Lemma RangeCheck_obligation3: forall (LIMIT_BIT_SIZE : nat) (messageId : F) (limit : F) (bitCheck : (list F)) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x90 => ((x90 = 0%F) \/ (x90 = 1%F))) bitCheck -> (((as_le_f bitCheck) = messageId) /\ ((length bitCheck) = LIMIT_BIT_SIZE)) -> True -> ((v = messageId) -> ((^ v) <= ((2%nat ^ LIMIT_BIT_SIZE)%Z - 1%nat)%Z)).
Proof. 
intros. intuition.
pose proof (as_le_f_lt bitCheck).
subst. auto.
Qed.

(* no range check on `limit`, since it is controlled by the sender  *)
Lemma RangeCheck_obligation4: forall (LIMIT_BIT_SIZE : nat) (messageId : F) (limit : F) (bitCheck : (list F)) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x91 => ((x91 = 0%F) \/ (x91 = 1%F))) bitCheck -> (((as_le_f bitCheck) = messageId) /\ ((length bitCheck) = LIMIT_BIT_SIZE)) -> True -> ((v = limit) -> ((^ v) <= ((2%nat ^ LIMIT_BIT_SIZE)%Z - 1%nat)%Z)).
Proof.
Admitted.

Lemma RangeCheck_obligation5: forall (LIMIT_BIT_SIZE : nat) (messageId : F) (limit : F) (bitCheck : (list F)) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x92 => ((x92 = 0%F) \/ (x92 = 1%F))) bitCheck -> (((as_le_f bitCheck) = messageId) /\ ((length bitCheck) = LIMIT_BIT_SIZE)) -> True -> ((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((^ messageId) < (^ limit))) /\ ((v = 0%F) -> ~((^ messageId) < (^ limit))))) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((^ messageId) < (^ limit))) /\ ((v = 0%F) -> ~((^ messageId) < (^ limit)))))).
Proof. hammer. Qed.



(* Withdraw *)
Lemma Withdraw_obligation0: forall (identitySecret : F) (address : F) (v : Z), True -> True -> True -> ((v = 1%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma Withdraw_obligation1: forall (identitySecret : F) (address : F) (v : (list F)), True -> True -> Forall (fun x0 => True) v -> True -> (((True /\ ((v!0%nat) = identitySecret)) /\ ((length v) = 1%nat)) -> ((length v) = 1%nat)).
Proof. hammer. Qed.

Lemma Withdraw_obligation2: forall (identitySecret : F) (address : F) (v : F), True -> True -> True -> ((v = (Poseidon 1%nat (identitySecret :: nil))) -> (v = (Poseidon 1%nat (identitySecret :: nil)))).
Proof. hammer. Qed.



(* RLN diff *)

Lemma RLN_obligation0: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (v : Z), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x0 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x1 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> ((v = 1%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma RLN_obligation1: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (v : (list F)), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x2 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x3 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> Forall (fun x4 => True) v -> True -> (((True /\ ((v!0%nat) = identitySecret)) /\ ((length v) = 1%nat)) -> ((length v) = 1%nat)).
Proof. hammer. Qed.

Lemma RLN_obligation2: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (v : Z), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x5 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x6 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> True -> ((v = 2%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma RLN_obligation3: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (v : (list F)), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x7 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x8 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> Forall (fun x9 => True) v -> True -> ((((True /\ ((v!0%nat) = identityCommitment)) /\ ((v!1%nat) = userMessageLimit)) /\ ((length v) = 2%nat)) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma RLN_obligation4: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (rateCommitment : F) (v : Z), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x10 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x11 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (rateCommitment = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) -> True -> (((0%nat <= v) /\ (v = DEPTH)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma RLN_obligation5_trivial: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (rateCommitment : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x12 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x13 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (rateCommitment = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) -> True -> (((v = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) /\ (v = rateCommitment)) -> True).
Proof. hammer. Qed.

Lemma RLN_obligation6: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (rateCommitment : F) (v : (list F)), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x14 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x15 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (rateCommitment = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) -> Forall (fun x16 => True) v -> True -> ((((length v) = DEPTH) /\ (v = identityPathIndex)) -> ((length v) = DEPTH)).
Proof. hammer. Qed.

Lemma RLN_obligation7: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (rateCommitment : F) (v : (list F)), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x17 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x18 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (rateCommitment = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) -> Forall (fun x19 => True) v -> True -> ((((length v) = DEPTH) /\ (v = pathElements)) -> ((length v) = DEPTH)).
Proof. hammer. Qed.

Lemma RLN_obligation8: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (rateCommitment : F) (root : F) (v : Z), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x20 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x21 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (rateCommitment = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) rateCommitment)) -> True -> ((((0%nat <= v) /\ ((v < 253%nat) /\ True)) /\ (v = LIMIT_BIT_SIZE)) -> ((0%nat <= v) /\ ((v < 253%nat) /\ True))).
Proof. hammer. Qed.

Lemma RLN_obligation9_trivial: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (rateCommitment : F) (root : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x22 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x23 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (rateCommitment = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) rateCommitment)) -> True -> ((v = messageId) -> True).
Proof. hammer. Qed.

Lemma RLN_obligation10_trivial: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (rateCommitment : F) (root : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x24 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x25 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (rateCommitment = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) rateCommitment)) -> True -> ((v = userMessageLimit) -> True).
Proof. hammer. Qed.

Lemma RLN_obligation11: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (rateCommitment : F) (root : F) (rangeCheck : F) (v : Z), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x26 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x27 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (rateCommitment = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) rateCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ userMessageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ userMessageLimit))))) -> True -> ((v = 3%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma RLN_obligation12: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (rateCommitment : F) (root : F) (rangeCheck : F) (v : (list F)), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x28 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x29 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (rateCommitment = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) rateCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ userMessageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ userMessageLimit))))) -> Forall (fun x30 => True) v -> True -> (((((True /\ ((v!0%nat) = identitySecret)) /\ ((v!1%nat) = externalNullifier)) /\ ((v!2%nat) = messageId)) /\ ((length v) = 3%nat)) -> ((length v) = 3%nat)).
Proof. hammer. Qed.

Lemma RLN_obligation13_trivial: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (rateCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x31 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x32 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (rateCommitment = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) rateCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ userMessageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ userMessageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> True -> ((v = identitySecret) -> True).
Proof. hammer. Qed.

Lemma RLN_obligation14_trivial: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (rateCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x33 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x34 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (rateCommitment = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) rateCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ userMessageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ userMessageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> True -> (((v = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) /\ (v = a1)) -> True).
Proof. hammer. Qed.

Lemma RLN_obligation15_trivial: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (rateCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x35 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x36 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (rateCommitment = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) rateCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ userMessageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ userMessageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> True -> ((v = x) -> True).
Proof. hammer. Qed.

Lemma RLN_obligation16_trivial: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (rateCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x37 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x38 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (rateCommitment = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) rateCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ userMessageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ userMessageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> True -> ((v = (a1 * x)%F) -> True).
Proof. hammer. Qed.

Lemma RLN_obligation17: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (rateCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (y : F) (v : Z), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x39 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x40 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (rateCommitment = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) rateCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ userMessageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ userMessageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> (y = (identitySecret + (a1 * x)%F)%F) -> True -> ((v = 1%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma RLN_obligation18: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (rateCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (y : F) (v : (list F)), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x41 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x42 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (rateCommitment = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) rateCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ userMessageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ userMessageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> (y = (identitySecret + (a1 * x)%F)%F) -> Forall (fun x43 => True) v -> True -> (((True /\ ((v!0%nat) = a1)) /\ ((length v) = 1%nat)) -> ((length v) = 1%nat)).
Proof. hammer. Qed.

Lemma RLN_obligation19: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (rateCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (y : F) (nullifier : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x44 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x45 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (rateCommitment = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) rateCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ userMessageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ userMessageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> (y = (identitySecret + (a1 * x)%F)%F) -> (nullifier = (Poseidon 1%nat (a1 :: nil))) -> True -> (((v = (identitySecret + (a1 * x)%F)%F) /\ (v = y)) -> (v = (identitySecret + ((Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil)))) * x)%F)%F)).
Proof. hammer. Qed.

Lemma RLN_obligation20: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (rateCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (y : F) (nullifier : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x46 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x47 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (rateCommitment = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) rateCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ userMessageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ userMessageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> (y = (identitySecret + (a1 * x)%F)%F) -> (nullifier = (Poseidon 1%nat (a1 :: nil))) -> True -> (((v = (MrklTreeInclPfHash (zip identityPathIndex pathElements) rateCommitment)) /\ (v = root)) -> (v = (MrklTreeInclPfHash (zip identityPathIndex pathElements) (Poseidon 2%nat ((Poseidon 1%nat (identitySecret :: nil)) :: (userMessageLimit :: nil)))))).
Proof. hammer. Qed.

Lemma RLN_obligation21: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (rateCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (y : F) (nullifier : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x48 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x49 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (rateCommitment = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) rateCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ userMessageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ userMessageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> (y = (identitySecret + (a1 * x)%F)%F) -> (nullifier = (Poseidon 1%nat (a1 :: nil))) -> True -> (((v = (Poseidon 1%nat (a1 :: nil))) /\ (v = nullifier)) -> (v = (Poseidon 1%nat ((Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil)))) :: nil)))).
Proof. hammer. Qed.

Lemma RLN_obligation22_trivial: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (userMessageLimit : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (identityCommitment : F) (rateCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (y : F) (nullifier : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> True -> Forall (fun x50 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x51 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (rateCommitment = (Poseidon 2%nat (identityCommitment :: (userMessageLimit :: nil)))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) rateCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ userMessageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ userMessageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> (y = (identitySecret + (a1 * x)%F)%F) -> (nullifier = (Poseidon 1%nat (a1 :: nil))) -> (True -> True).
Proof. hammer. Qed.



(* RLN same *)
Lemma RLN_same_obligation0: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (v : Z), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x0 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x1 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> True -> ((v = 1%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma RLN_same_obligation1: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (v : (list F)), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x2 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x3 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> Forall (fun x4 => True) v -> True -> (((True /\ ((v!0%nat) = identitySecret)) /\ ((length v) = 1%nat)) -> ((length v) = 1%nat)).
Proof. hammer. Qed.

Lemma RLN_same_obligation2: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (identityCommitment : F) (v : Z), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x5 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x6 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> True -> (((0%nat <= v) /\ (v = DEPTH)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma RLN_same_obligation3_trivial: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (identityCommitment : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x7 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x8 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> True -> (((v = (Poseidon 1%nat (identitySecret :: nil))) /\ (v = identityCommitment)) -> True).
Proof. hammer. Qed.

Lemma RLN_same_obligation4: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (identityCommitment : F) (v : (list F)), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x9 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x10 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> Forall (fun x11 => True) v -> True -> ((((length v) = DEPTH) /\ (v = identityPathIndex)) -> ((length v) = DEPTH)).
Proof. hammer. Qed.

Lemma RLN_same_obligation5: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (identityCommitment : F) (v : (list F)), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x12 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x13 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> Forall (fun x14 => True) v -> True -> ((((length v) = DEPTH) /\ (v = pathElements)) -> ((length v) = DEPTH)).
Proof. hammer. Qed.

Lemma RLN_same_obligation6: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (identityCommitment : F) (root : F) (v : Z), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x15 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x16 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) identityCommitment)) -> True -> ((((0%nat <= v) /\ ((v < 253%nat) /\ True)) /\ (v = LIMIT_BIT_SIZE)) -> ((0%nat <= v) /\ ((v < 253%nat) /\ True))).
Proof. hammer. Qed.

Lemma RLN_same_obligation7_trivial: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (identityCommitment : F) (root : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x17 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x18 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) identityCommitment)) -> True -> ((v = messageId) -> True).
Proof. hammer. Qed.

Lemma RLN_same_obligation8_trivial: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (identityCommitment : F) (root : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x19 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x20 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) identityCommitment)) -> True -> ((v = messageLimit) -> True).
Proof. hammer. Qed.

Lemma RLN_same_obligation9: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (identityCommitment : F) (root : F) (rangeCheck : F) (v : Z), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x21 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x22 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) identityCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ messageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ messageLimit))))) -> True -> ((v = 3%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma RLN_same_obligation10: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (identityCommitment : F) (root : F) (rangeCheck : F) (v : (list F)), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x23 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x24 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) identityCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ messageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ messageLimit))))) -> Forall (fun x25 => True) v -> True -> (((((True /\ ((v!0%nat) = identitySecret)) /\ ((v!1%nat) = externalNullifier)) /\ ((v!2%nat) = messageId)) /\ ((length v) = 3%nat)) -> ((length v) = 3%nat)).
Proof. hammer. Qed.

Lemma RLN_same_obligation11_trivial: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (identityCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x26 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x27 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) identityCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ messageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ messageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> True -> ((v = identitySecret) -> True).
Proof. hammer. Qed.

Lemma RLN_same_obligation12_trivial: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (identityCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x28 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x29 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) identityCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ messageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ messageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> True -> (((v = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) /\ (v = a1)) -> True).
Proof. hammer. Qed.

Lemma RLN_same_obligation13_trivial: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (identityCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x30 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x31 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) identityCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ messageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ messageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> True -> ((v = x) -> True).
Proof. hammer. Qed.

Lemma RLN_same_obligation14_trivial: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (identityCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x32 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x33 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) identityCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ messageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ messageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> True -> ((v = (a1 * x)%F) -> True).
Proof. hammer. Qed.

Lemma RLN_same_obligation15: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (identityCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (y : F) (v : Z), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x34 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x35 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) identityCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ messageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ messageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> (y = (identitySecret + (a1 * x)%F)%F) -> True -> ((v = 1%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma RLN_same_obligation16: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (identityCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (y : F) (v : (list F)), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x36 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x37 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) identityCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ messageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ messageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> (y = (identitySecret + (a1 * x)%F)%F) -> Forall (fun x38 => True) v -> True -> (((True /\ ((v!0%nat) = a1)) /\ ((length v) = 1%nat)) -> ((length v) = 1%nat)).
Proof. hammer. Qed.

Lemma RLN_same_obligation17: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (identityCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (y : F) (nullifier : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x39 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x40 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) identityCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ messageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ messageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> (y = (identitySecret + (a1 * x)%F)%F) -> (nullifier = (Poseidon 1%nat (a1 :: nil))) -> True -> (((v = (identitySecret + (a1 * x)%F)%F) /\ (v = y)) -> (v = (identitySecret + ((Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil)))) * x)%F)%F)).
Proof. hammer. Qed.

Lemma RLN_same_obligation18: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (identityCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (y : F) (nullifier : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x41 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x42 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) identityCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ messageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ messageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> (y = (identitySecret + (a1 * x)%F)%F) -> (nullifier = (Poseidon 1%nat (a1 :: nil))) -> True -> (((v = (MrklTreeInclPfHash (zip identityPathIndex pathElements) identityCommitment)) /\ (v = root)) -> (v = (MrklTreeInclPfHash (zip identityPathIndex pathElements) (Poseidon 1%nat (identitySecret :: nil))))).
Proof. hammer. Qed.

Lemma RLN_same_obligation19: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (identityCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (y : F) (nullifier : F) (v : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x43 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x44 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) identityCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ messageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ messageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> (y = (identitySecret + (a1 * x)%F)%F) -> (nullifier = (Poseidon 1%nat (a1 :: nil))) -> True -> (((v = (Poseidon 1%nat (a1 :: nil))) /\ (v = nullifier)) -> (v = (Poseidon 1%nat ((Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil)))) :: nil)))).
Proof. hammer. Qed.

Lemma RLN_same_obligation20_trivial: forall (DEPTH : nat) (LIMIT_BIT_SIZE : nat) (identitySecret : F) (messageId : F) (pathElements : (list F)) (identityPathIndex : (list F)) (x : F) (externalNullifier : F) (messageLimit : F) (identityCommitment : F) (root : F) (rangeCheck : F) (a1 : F) (y : F) (nullifier : F), ((LIMIT_BIT_SIZE < 253%nat) /\ True) -> True -> True -> Forall (fun x45 => True) pathElements -> ((length pathElements) = DEPTH) -> Forall (fun x46 => True) identityPathIndex -> ((length identityPathIndex) = DEPTH) -> True -> True -> True -> (identityCommitment = (Poseidon 1%nat (identitySecret :: nil))) -> (root = (MrklTreeInclPfHash (zip identityPathIndex pathElements) identityCommitment)) -> (((rangeCheck = 0%F) \/ (rangeCheck = 1%F)) /\ (((rangeCheck = 1%F) -> ((^ messageId) < (^ messageLimit))) /\ ((rangeCheck = 0%F) -> ~((^ messageId) < (^ messageLimit))))) -> (a1 = (Poseidon 3%nat (identitySecret :: (externalNullifier :: (messageId :: nil))))) -> (y = (identitySecret + (a1 * x)%F)%F) -> (nullifier = (Poseidon 1%nat (a1 :: nil))) -> (True -> True).
Proof. hammer. Qed.