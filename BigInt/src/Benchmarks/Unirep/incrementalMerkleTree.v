(** * DSL benchmark: Semaphore *)

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

Lemma MerkleTreeInclusionProof_obligation0_trivial: forall (n_levels : nat) (leaf : F) (path_index : (list F)) (path_elements : (list F)) (z : (list (F * F))) (v : Z), True -> Forall (fun x0 => True) path_index -> ((length path_index) = n_levels) -> Forall (fun x1 => True) path_elements -> ((length path_elements) = n_levels) -> Forall (fun x4 => match x4 with (x2,x3) => True end) z -> Forall (fun x4 => match x4 with (x2,x3) => True end) z -> Forall (fun x4 => match x4 with (x2,x3) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length path_index) -> (((fst (z!iz)) = (path_index!iz)) /\ ((snd (z!iz)) = (path_elements!iz)))) /\ ((length z) = (length path_index))) -> True -> ((v = 0%nat) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation1_trivial: forall (n_levels : nat) (leaf : F) (path_index : (list F)) (path_elements : (list F)) (z : (list (F * F))) (v : Z), True -> Forall (fun x5 => True) path_index -> ((length path_index) = n_levels) -> Forall (fun x6 => True) path_elements -> ((length path_elements) = n_levels) -> Forall (fun x9 => match x9 with (x7,x8) => True end) z -> Forall (fun x9 => match x9 with (x7,x8) => True end) z -> Forall (fun x9 => match x9 with (x7,x8) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length path_index) -> (((fst (z!iz)) = (path_index!iz)) /\ ((snd (z!iz)) = (path_elements!iz)))) /\ ((length z) = (length path_index))) -> True -> (((0%nat <= v) /\ (v = n_levels)) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation2_trivial: forall (n_levels : nat) (leaf : F) (path_index : (list F)) (path_elements : (list F)) (z : (list (F * F))) (v : Z), True -> Forall (fun x10 => True) path_index -> ((length path_index) = n_levels) -> Forall (fun x11 => True) path_elements -> ((length path_elements) = n_levels) -> Forall (fun x14 => match x14 with (x12,x13) => True end) z -> Forall (fun x14 => match x14 with (x12,x13) => True end) z -> Forall (fun x14 => match x14 with (x12,x13) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length path_index) -> (((fst (z!iz)) = (path_index!iz)) /\ ((snd (z!iz)) = (path_elements!iz)))) /\ ((length z) = (length path_index))) -> True -> (((0%nat <= v) /\ (v < n_levels)) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation3_trivial: forall (n_levels : nat) (leaf : F) (path_index : (list F)) (path_elements : (list F)) (z : (list (F * F))) (_i : nat) (v : F), True -> Forall (fun x15 => True) path_index -> ((length path_index) = n_levels) -> Forall (fun x16 => True) path_elements -> ((length path_elements) = n_levels) -> Forall (fun x19 => match x19 with (x17,x18) => True end) z -> Forall (fun x19 => match x19 with (x17,x18) => True end) z -> Forall (fun x19 => match x19 with (x17,x18) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length path_index) -> (((fst (z!iz)) = (path_index!iz)) /\ ((snd (z!iz)) = (path_elements!iz)))) /\ ((length z) = (length path_index))) -> (_i < n_levels) -> True -> ((v = (MrklTreeInclPfHash (take _i z) leaf)) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation4_trivial: forall (n_levels : nat) (leaf : F) (path_index : (list F)) (path_elements : (list F)) (z : (list (F * F))) (_i : nat) (x : F) (v : F), True -> Forall (fun x20 => True) path_index -> ((length path_index) = n_levels) -> Forall (fun x21 => True) path_elements -> ((length path_elements) = n_levels) -> Forall (fun x24 => match x24 with (x22,x23) => True end) z -> Forall (fun x24 => match x24 with (x22,x23) => True end) z -> Forall (fun x24 => match x24 with (x22,x23) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length path_index) -> (((fst (z!iz)) = (path_index!iz)) /\ ((snd (z!iz)) = (path_elements!iz)))) /\ ((length z) = (length path_index))) -> (_i < n_levels) -> (x = (MrklTreeInclPfHash (take _i z) leaf)) -> True -> ((v = 1%F) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation5_trivial: forall (n_levels : nat) (leaf : F) (path_index : (list F)) (path_elements : (list F)) (z : (list (F * F))) (_i : nat) (x : F) (v : F), True -> Forall (fun x25 => True) path_index -> ((length path_index) = n_levels) -> Forall (fun x26 => True) path_elements -> ((length path_elements) = n_levels) -> Forall (fun x29 => match x29 with (x27,x28) => True end) z -> Forall (fun x29 => match x29 with (x27,x28) => True end) z -> Forall (fun x29 => match x29 with (x27,x28) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length path_index) -> (((fst (z!iz)) = (path_index!iz)) /\ ((snd (z!iz)) = (path_elements!iz)))) /\ ((length z) = (length path_index))) -> (_i < n_levels) -> (x = (MrklTreeInclPfHash (take _i z) leaf)) -> True -> ((v = (1%F - (fst (z!_i)))%F) -> True).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation6: forall (n_levels : nat) (leaf : F) (path_index : (list F)) (path_elements : (list F)) (z : (list (F * F))) (_i : nat) (x : F) (u0 : unit) (c : (list (list F))) (v : Z), True -> Forall (fun x30 => True) path_index -> ((length path_index) = n_levels) -> Forall (fun x31 => True) path_elements -> ((length path_elements) = n_levels) -> Forall (fun x34 => match x34 with (x32,x33) => True end) z -> Forall (fun x34 => match x34 with (x32,x33) => True end) z -> Forall (fun x34 => match x34 with (x32,x33) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length path_index) -> (((fst (z!iz)) = (path_index!iz)) /\ ((snd (z!iz)) = (path_elements!iz)))) /\ ((length z) = (length path_index))) -> (_i < n_levels) -> (x = (MrklTreeInclPfHash (take _i z) leaf)) -> (((fst (z!_i)) * (1%F - (fst (z!_i)))%F)%F = 0%F) -> Forall (fun x36 => Forall (fun x35 => True) x36) c -> Forall (fun x36 => ((length x36) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: ((snd (z!_i)) :: nil)))) /\ ((c!1%nat) = ((snd (z!_i)) :: (x :: nil)))) /\ ((length c) = 2%nat)) -> True -> ((v = 2%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation7: forall (n_levels : nat) (leaf : F) (path_index : (list F)) (path_elements : (list F)) (z : (list (F * F))) (_i : nat) (x : F) (u0 : unit) (c : (list (list F))) (v : (list (list F))), True -> Forall (fun x37 => True) path_index -> ((length path_index) = n_levels) -> Forall (fun x38 => True) path_elements -> ((length path_elements) = n_levels) -> Forall (fun x41 => match x41 with (x39,x40) => True end) z -> Forall (fun x41 => match x41 with (x39,x40) => True end) z -> Forall (fun x41 => match x41 with (x39,x40) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length path_index) -> (((fst (z!iz)) = (path_index!iz)) /\ ((snd (z!iz)) = (path_elements!iz)))) /\ ((length z) = (length path_index))) -> (_i < n_levels) -> (x = (MrklTreeInclPfHash (take _i z) leaf)) -> (((fst (z!_i)) * (1%F - (fst (z!_i)))%F)%F = 0%F) -> Forall (fun x43 => Forall (fun x42 => True) x43) c -> Forall (fun x43 => ((length x43) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: ((snd (z!_i)) :: nil)))) /\ ((c!1%nat) = ((snd (z!_i)) :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x45 => Forall (fun x44 => True) x45) v -> Forall (fun x45 => ((length x45) = 2%nat)) v -> True -> (((((True /\ ((v!0%nat) = (x :: ((snd (z!_i)) :: nil)))) /\ ((v!1%nat) = ((snd (z!_i)) :: (x :: nil)))) /\ ((length v) = 2%nat)) /\ (v = c)) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation8: forall (n_levels : nat) (leaf : F) (path_index : (list F)) (path_elements : (list F)) (z : (list (F * F))) (_i : nat) (x : F) (u0 : unit) (c : (list (list F))) (v : (list F)), True -> Forall (fun x46 => True) path_index -> ((length path_index) = n_levels) -> Forall (fun x47 => True) path_elements -> ((length path_elements) = n_levels) -> Forall (fun x50 => match x50 with (x48,x49) => True end) z -> Forall (fun x50 => match x50 with (x48,x49) => True end) z -> Forall (fun x50 => match x50 with (x48,x49) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length path_index) -> (((fst (z!iz)) = (path_index!iz)) /\ ((snd (z!iz)) = (path_elements!iz)))) /\ ((length z) = (length path_index))) -> (_i < n_levels) -> (x = (MrklTreeInclPfHash (take _i z) leaf)) -> (((fst (z!_i)) * (1%F - (fst (z!_i)))%F)%F = 0%F) -> Forall (fun x52 => Forall (fun x51 => True) x52) c -> Forall (fun x52 => ((length x52) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: ((snd (z!_i)) :: nil)))) /\ ((c!1%nat) = ((snd (z!_i)) :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x53 => True) v -> True -> (((length v) = 2%nat) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation9: forall (n_levels : nat) (leaf : F) (path_index : (list F)) (path_elements : (list F)) (z : (list (F * F))) (_i : nat) (x : F) (u0 : unit) (c : (list (list F))) (m : (list F)) (v : Z), True -> Forall (fun x54 => True) path_index -> ((length path_index) = n_levels) -> Forall (fun x55 => True) path_elements -> ((length path_elements) = n_levels) -> Forall (fun x58 => match x58 with (x56,x57) => True end) z -> Forall (fun x58 => match x58 with (x56,x57) => True end) z -> Forall (fun x58 => match x58 with (x56,x57) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length path_index) -> (((fst (z!iz)) = (path_index!iz)) /\ ((snd (z!iz)) = (path_elements!iz)))) /\ ((length z) = (length path_index))) -> (_i < n_levels) -> (x = (MrklTreeInclPfHash (take _i z) leaf)) -> (((fst (z!_i)) * (1%F - (fst (z!_i)))%F)%F = 0%F) -> Forall (fun x60 => Forall (fun x59 => True) x60) c -> Forall (fun x60 => ((length x60) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: ((snd (z!_i)) :: nil)))) /\ ((c!1%nat) = ((snd (z!_i)) :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x61 => True) m -> ((forall (i:nat), 0%nat <= i < 2%nat -> ((m!i) = (((((c!i)!1%nat) - ((c!i)!0%nat))%F * (fst (z!_i)))%F + ((c!i)!0%nat))%F)) /\ ((length m) = 2%nat)) -> True -> ((v = 2%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation10: forall (n_levels : nat) (leaf : F) (path_index : (list F)) (path_elements : (list F)) (z : (list (F * F))) (_i : nat) (x : F) (u0 : unit) (c : (list (list F))) (m : (list F)) (v : (list F)), True -> Forall (fun x62 => True) path_index -> ((length path_index) = n_levels) -> Forall (fun x63 => True) path_elements -> ((length path_elements) = n_levels) -> Forall (fun x66 => match x66 with (x64,x65) => True end) z -> Forall (fun x66 => match x66 with (x64,x65) => True end) z -> Forall (fun x66 => match x66 with (x64,x65) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length path_index) -> (((fst (z!iz)) = (path_index!iz)) /\ ((snd (z!iz)) = (path_elements!iz)))) /\ ((length z) = (length path_index))) -> (_i < n_levels) -> (x = (MrklTreeInclPfHash (take _i z) leaf)) -> (((fst (z!_i)) * (1%F - (fst (z!_i)))%F)%F = 0%F) -> Forall (fun x68 => Forall (fun x67 => True) x68) c -> Forall (fun x68 => ((length x68) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: ((snd (z!_i)) :: nil)))) /\ ((c!1%nat) = ((snd (z!_i)) :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x69 => True) m -> ((forall (i:nat), 0%nat <= i < 2%nat -> ((m!i) = (((((c!i)!1%nat) - ((c!i)!0%nat))%F * (fst (z!_i)))%F + ((c!i)!0%nat))%F)) /\ ((length m) = 2%nat)) -> Forall (fun x70 => True) v -> True -> ((((forall (i:nat), 0%nat <= i < 2%nat -> ((v!i) = (((((c!i)!1%nat) - ((c!i)!0%nat))%F * (fst (z!_i)))%F + ((c!i)!0%nat))%F)) /\ ((length v) = 2%nat)) /\ (v = m)) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation11: forall (n_levels : nat) (leaf : F) (path_index : (list F)) (path_elements : (list F)) (z : (list (F * F))) (_i : nat) (x : F) (u0 : unit) (c : (list (list F))) (m : (list F)) (v : F), True -> Forall (fun x71 => True) path_index -> ((length path_index) = n_levels) -> Forall (fun x72 => True) path_elements -> ((length path_elements) = n_levels) -> Forall (fun x75 => match x75 with (x73,x74) => True end) z -> Forall (fun x75 => match x75 with (x73,x74) => True end) z -> Forall (fun x75 => match x75 with (x73,x74) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length path_index) -> (((fst (z!iz)) = (path_index!iz)) /\ ((snd (z!iz)) = (path_elements!iz)))) /\ ((length z) = (length path_index))) -> (_i < n_levels) -> (x = (MrklTreeInclPfHash (take _i z) leaf)) -> (((fst (z!_i)) * (1%F - (fst (z!_i)))%F)%F = 0%F) -> Forall (fun x77 => Forall (fun x76 => True) x77) c -> Forall (fun x77 => ((length x77) = 2%nat)) c -> (((True /\ ((c!0%nat) = (x :: ((snd (z!_i)) :: nil)))) /\ ((c!1%nat) = ((snd (z!_i)) :: (x :: nil)))) /\ ((length c) = 2%nat)) -> Forall (fun x78 => True) m -> ((forall (i:nat), 0%nat <= i < 2%nat -> ((m!i) = (((((c!i)!1%nat) - ((c!i)!0%nat))%F * (fst (z!_i)))%F + ((c!i)!0%nat))%F)) /\ ((length m) = 2%nat)) -> True -> ((v = (Poseidon 2%nat m)) -> (v = (MrklTreeInclPfHash (take (_i + 1%nat)%nat z) leaf))).
Proof. 
intuition; subst; unfold MrklTreeInclPfHash, take in *; simpl in *;unwrap_C.
specialize (H13 0%nat) as Hm1; specialize (H13 1%nat) as Hm2; simpl in *.
assert ((c!1)!0%nat = snd (z ! _i)). { rewrite H22. auto. } 
assert ((c!0)!1%nat = snd (z ! _i)). { rewrite H23. auto. }
assert ((c!1)!1%nat = fold_left (fun (y : F) (x : F * F) => if dec (fst x = 0)%F then Poseidon 2 (y :: snd x :: nil) else Poseidon 2 (snd x :: y :: nil)) (z [:_i]) leaf). 
{ rewrite H22. auto. }
assert ((c!0)!0%nat = fold_left (fun (y : F) (x : F * F) => if dec (fst x = 0)%F then Poseidon 2 (y :: snd x :: nil) else Poseidon 2 (snd x :: y :: nil)) (z [:_i]) leaf). 
{ rewrite H23. auto. }
rewrite H1, H9, H15, H17 in *. rewrite Poseidon_2;auto. 
replace (_i + 1)%nat with (S _i) by lia. rewrite fold_left_firstn_S; auto.
destruct dec.
- rewrite e in *. 
  assert (m ! 1 = snd (z ! _i)). 
  { rewrite Hm2;auto. rewrite Fmul_0_r. rewrite Fadd_0_l. auto. }
  assert (m ! 0 = (c ! 1) ! 1).
  { rewrite Hm1;auto. rewrite Fmul_0_r. rewrite Fadd_0_l. auto. }
  rewrite H24, H25. rewrite H15. auto.
- assert (fst (z ! _i) = 1%F). { fqsatz. }
  rewrite H24 in *.
  assert (m ! 1 = (c ! 1) ! 1) by (rewrite Hm2;auto;try fqsatz).
  assert (m ! 0 = snd (z ! _i)) by (rewrite Hm1;auto;try fqsatz).
  rewrite H25, H26. rewrite H15. auto.
Qed.

Lemma MerkleTreeInclusionProof_obligation12: forall (n_levels : nat) (leaf : F) (path_index : (list F)) (path_elements : (list F)) (z : (list (F * F))) (v : F), True -> Forall (fun x79 => True) path_index -> ((length path_index) = n_levels) -> Forall (fun x80 => True) path_elements -> ((length path_elements) = n_levels) -> Forall (fun x83 => match x83 with (x81,x82) => True end) z -> Forall (fun x83 => match x83 with (x81,x82) => True end) z -> Forall (fun x83 => match x83 with (x81,x82) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length path_index) -> (((fst (z!iz)) = (path_index!iz)) /\ ((snd (z!iz)) = (path_elements!iz)))) /\ ((length z) = (length path_index))) -> True -> ((v = leaf) -> (v = (MrklTreeInclPfHash (take 0%nat z) leaf))).
Proof. hammer. Qed.

Lemma MerkleTreeInclusionProof_obligation13: forall (n_levels : nat) (leaf : F) (path_index : (list F)) (path_elements : (list F)) (z : (list (F * F))) (v : F), True -> Forall (fun x84 => True) path_index -> ((length path_index) = n_levels) -> Forall (fun x85 => True) path_elements -> ((length path_elements) = n_levels) -> Forall (fun x88 => match x88 with (x86,x87) => True end) z -> Forall (fun x88 => match x88 with (x86,x87) => True end) z -> Forall (fun x88 => match x88 with (x86,x87) => True end) z -> ((forall (iz:nat), 0%nat <= iz < (length path_index) -> (((fst (z!iz)) = (path_index!iz)) /\ ((snd (z!iz)) = (path_elements!iz)))) /\ ((length z) = (length path_index))) -> True -> ((v = (MrklTreeInclPfHash (take n_levels z) leaf)) -> (v = (MrklTreeInclPfHash (zip path_index path_elements) leaf))).
Proof. 
  intuition; unwrap_C.
  unfold zip, take in *; simpl in *.
  assert (z = combine path_index path_elements).
  { apply list_combine_eq_forall;auto. }
  rewrite <- H7. rewrite H1 in H11. rewrite <- H11 in H9.
  erewrite ListUtil.List.firstn_all in H9;auto.
Qed.

(* EpochKeyHasher *)

Lemma EpochKeyHasher_obligation0: forall (identity_secret : F) (attester_id : F) (epoch : F) (nonce : F) (v : Z), True -> True -> True -> True -> True -> ((v = 2%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma EpochKeyHasher_obligation1: forall (identity_secret : F) (attester_id : F) (epoch : F) (nonce : F) (v : (list F)), True -> True -> True -> True -> Forall (fun x0 => True) v -> True -> ((((True /\ ((v!0%nat) = identity_secret)) /\ ((v!1%nat) = (attester_id + (((2%F ^ 160%nat)%F * epoch)%F + ((2%F ^ 208%nat)%F * nonce)%F)%F)%F)) /\ ((length v) = 2%nat)) -> ((length v) = 2%nat)).
Proof. hammer. Qed.
Lemma EpochKeyHasher_obligation2: forall (identity_secret : F) (attester_id : F) (epoch : F) (nonce : F) (v : F), True -> True -> True -> True -> True -> ((v = (Poseidon 2%nat (identity_secret :: ((attester_id + (((2%F ^ 160%nat)%F * epoch)%F + ((2%F ^ 208%nat)%F * nonce)%F)%F)%F :: nil)))) -> (v = (Poseidon 2%nat (identity_secret :: ((attester_id + (((2%F ^ 160%nat)%F * epoch)%F + ((2%F ^ 208%nat)%F * nonce)%F)%F)%F :: nil))))).
Proof. hammer. Qed.

(* EpochTreeLeaf *)

Definition u_epoch_tree_leaf (a:list F) (b:F) := fold_left (fun (x:F) (y:F) => Poseidon 2%nat (x::y::nil)) a b.

Lemma EpochTreeLeaf_obligation0_trivial: forall (FIELD_COUNT : nat) (epoch_key : F) (data : (list F)) (v : Z), True -> Forall (fun x0 => True) data -> ((length data) = FIELD_COUNT) -> True -> ((v = 0%nat) -> True).
Proof. hammer. Qed.

Lemma EpochTreeLeaf_obligation1_trivial: forall (FIELD_COUNT : nat) (epoch_key : F) (data : (list F)) (v : Z), True -> Forall (fun x1 => True) data -> ((length data) = FIELD_COUNT) -> True -> (((0%nat <= v) /\ (v = FIELD_COUNT)) -> True).
Proof. hammer. Qed.

Lemma EpochTreeLeaf_obligation2_trivial: forall (FIELD_COUNT : nat) (epoch_key : F) (data : (list F)) (v : Z), True -> Forall (fun x2 => True) data -> ((length data) = FIELD_COUNT) -> True -> (((0%nat <= v) /\ (v < FIELD_COUNT)) -> True).
Proof. hammer. Qed.

Lemma EpochTreeLeaf_obligation3_trivial: forall (FIELD_COUNT : nat) (epoch_key : F) (data : (list F)) (i : nat) (v : F), True -> Forall (fun x3 => True) data -> ((length data) = FIELD_COUNT) -> (i < FIELD_COUNT) -> True -> ((v = (u_epoch_tree_leaf (data[:i]) epoch_key)) -> True).
Proof. hammer. Qed.

Lemma EpochTreeLeaf_obligation4: forall (FIELD_COUNT : nat) (epoch_key : F) (data : (list F)) (i : nat) (x : F) (v : Z), True -> Forall (fun x4 => True) data -> ((length data) = FIELD_COUNT) -> (i < FIELD_COUNT) -> (x = (u_epoch_tree_leaf (data[:i]) epoch_key)) -> True -> ((v = 2%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma EpochTreeLeaf_obligation5: forall (FIELD_COUNT : nat) (epoch_key : F) (data : (list F)) (i : nat) (x : F) (v : (list F)), True -> Forall (fun x5 => True) data -> ((length data) = FIELD_COUNT) -> (i < FIELD_COUNT) -> (x = (u_epoch_tree_leaf (data[:i]) epoch_key)) -> Forall (fun x6 => True) v -> True -> ((((True /\ ((v!0%nat) = x)) /\ ((v!1%nat) = (data!i))) /\ ((length v) = 2%nat)) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma EpochTreeLeaf_obligation6: forall (FIELD_COUNT : nat) (epoch_key : F) (data : (list F)) (i : nat) (x : F) (v : F), True -> Forall (fun x7 => True) data -> ((length data) = FIELD_COUNT) -> (i < FIELD_COUNT) -> (x = (u_epoch_tree_leaf (data[:i]) epoch_key)) -> True -> ((v = (Poseidon 2%nat (x :: ((data!i) :: nil)))) -> (v = (u_epoch_tree_leaf (data[:(i + 1%nat)%nat]) epoch_key))).
Proof. 
  intros;subst.
  unfold u_epoch_tree_leaf.
  replace (i+1)%nat with (S i);try lia.
  rewrite fold_left_firstn_S';try lia.
  hammer. 
Qed.

Lemma EpochTreeLeaf_obligation7: forall (FIELD_COUNT : nat) (epoch_key : F) (data : (list F)) (v : F), True -> Forall (fun x8 => True) data -> ((length data) = FIELD_COUNT) -> True -> ((v = epoch_key) -> (v = (u_epoch_tree_leaf (data[:0%nat]) epoch_key))).
Proof. hammer. Qed.

Lemma EpochTreeLeaf_obligation8: forall (FIELD_COUNT : nat) (epoch_key : F) (data : (list F)) (v : F), True -> Forall (fun x9 => True) data -> ((length data) = FIELD_COUNT) -> True -> ((v = (u_epoch_tree_leaf (data[:FIELD_COUNT]) epoch_key)) -> (v = (u_epoch_tree_leaf data epoch_key))).
Proof. 
  intros. rewrite <- H1 in H3.
  rewrite ListUtil.List.firstn_all in H3. auto.
Qed.

(* StateTreeLeaf *)
Definition u_state_tree_leaf (a:list F) (b:F) := fold_left (fun (x:F) (y:F) => Poseidon 2%nat (x::y::nil)) a b.
Lemma StateTreeLeaf_obligation0_trivial: forall (FIELD_COUNT : nat) (data : (list F)) (identity_secret : F) (attester_id : F) (epoch : F) (v : Z), Forall (fun x0 => True) data -> ((length data) = FIELD_COUNT) -> True -> True -> True -> True -> ((v = 0%nat) -> True).
Proof. hammer. Qed.

Lemma StateTreeLeaf_obligation1_trivial: forall (FIELD_COUNT : nat) (data : (list F)) (identity_secret : F) (attester_id : F) (epoch : F) (v : Z), Forall (fun x1 => True) data -> ((length data) = FIELD_COUNT) -> True -> True -> True -> True -> (((0%nat <= v) /\ (v = FIELD_COUNT)) -> True).
Proof. hammer. Qed.

Lemma StateTreeLeaf_obligation2_trivial: forall (FIELD_COUNT : nat) (data : (list F)) (identity_secret : F) (attester_id : F) (epoch : F) (v : Z), Forall (fun x2 => True) data -> ((length data) = FIELD_COUNT) -> True -> True -> True -> True -> ((v = 1%nat) -> True).
Proof. hammer. Qed.

Lemma StateTreeLeaf_obligation3_trivial: forall (FIELD_COUNT : nat) (data : (list F)) (identity_secret : F) (attester_id : F) (epoch : F) (v : Z), Forall (fun x3 => True) data -> ((length data) = FIELD_COUNT) -> True -> True -> True -> True -> ((v = (FIELD_COUNT - 1%nat)%nat) -> True).
Proof. hammer. Qed.

Lemma StateTreeLeaf_obligation4_trivial: forall (FIELD_COUNT : nat) (data : (list F)) (identity_secret : F) (attester_id : F) (epoch : F) (v : Z), Forall (fun x4 => True) data -> ((length data) = FIELD_COUNT) -> True -> True -> True -> True -> (((0%nat <= v) /\ (v < (FIELD_COUNT - 1%nat)%nat)) -> True).
Proof. hammer. Qed.

Lemma StateTreeLeaf_obligation5_trivial: forall (FIELD_COUNT : nat) (data : (list F)) (identity_secret : F) (attester_id : F) (epoch : F) (i : nat) (v : F), Forall (fun x5 => True) data -> ((length data) = FIELD_COUNT) -> True -> True -> True -> (i < (FIELD_COUNT - 1%nat)%nat) -> True -> ((v = (u_state_tree_leaf ((skipn 1%nat data)[:i]) (data!0%nat))) -> True).
Proof. hammer. Qed.

Lemma StateTreeLeaf_obligation6: forall (FIELD_COUNT : nat) (data : (list F)) (identity_secret : F) (attester_id : F) (epoch : F) (i : nat) (x : F) (v : Z), Forall (fun x6 => True) data -> ((length data) = FIELD_COUNT) -> True -> True -> True -> (i < (FIELD_COUNT - 1%nat)%nat) -> (x = (u_state_tree_leaf ((skipn 1%nat data)[:i]) (data!0%nat))) -> True -> ((v = 2%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma StateTreeLeaf_obligation7: forall (FIELD_COUNT : nat) (data : (list F)) (identity_secret : F) (attester_id : F) (epoch : F) (i : nat) (x : F) (v : (list F)), Forall (fun x7 => True) data -> ((length data) = FIELD_COUNT) -> True -> True -> True -> (i < (FIELD_COUNT - 1%nat)%nat) -> (x = (u_state_tree_leaf ((skipn 1%nat data)[:i]) (data!0%nat))) -> Forall (fun x8 => True) v -> True -> ((((True /\ ((v!0%nat) = x)) /\ ((v!1%nat) = ((skipn 1%nat data)!i))) /\ ((length v) = 2%nat)) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma StateTreeLeaf_obligation8: forall (FIELD_COUNT : nat) (data : (list F)) (identity_secret : F) (attester_id : F) (epoch : F) (i : nat) (x : F) (v : F), Forall (fun x9 => True) data -> ((length data) = FIELD_COUNT) -> True -> True -> True -> (i < (FIELD_COUNT - 1%nat)%nat) -> (x = (u_state_tree_leaf ((skipn 1%nat data)[:i]) (data!0%nat))) -> True -> ((v = (Poseidon 2%nat (x :: (((skipn 1%nat data)!i) :: nil)))) -> (v = (u_state_tree_leaf ((skipn 1%nat data)[:(i + 1%nat)%nat]) (data!0%nat)))).
Proof. 
  intros;subst.
  unfold u_state_tree_leaf.
  replace (i+1)%nat with (S i);try lia.
  rewrite fold_left_firstn_S';try hammer.
Qed.

Lemma StateTreeLeaf_obligation9: forall (FIELD_COUNT : nat) (data : (list F)) (identity_secret : F) (attester_id : F) (epoch : F) (v : F), Forall (fun x10 => True) data -> ((length data) = FIELD_COUNT) -> True -> True -> True -> True -> ((v = (data!0%nat)) -> (v = (u_state_tree_leaf ((skipn 1%nat data)[:0%nat]) (data!0%nat)))).
Proof. hammer. Qed.

Lemma StateTreeLeaf_obligation10: forall (FIELD_COUNT : nat) (data : (list F)) (identity_secret : F) (attester_id : F) (epoch : F) (out1 : F) (v : Z), Forall (fun x11 => True) data -> ((length data) = FIELD_COUNT) -> True -> True -> True -> (out1 = (u_state_tree_leaf ((skipn 1%nat data)[:(FIELD_COUNT - 1%nat)%nat]) (data!0%nat))) -> True -> ((v = 3%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma StateTreeLeaf_obligation11: forall (FIELD_COUNT : nat) (data : (list F)) (identity_secret : F) (attester_id : F) (epoch : F) (out1 : F) (v : (list F)), Forall (fun x12 => True) data -> ((length data) = FIELD_COUNT) -> True -> True -> True -> (out1 = (u_state_tree_leaf ((skipn 1%nat data)[:(FIELD_COUNT - 1%nat)%nat]) (data!0%nat))) -> Forall (fun x13 => True) v -> True -> (((((True /\ ((v!0%nat) = identity_secret)) /\ ((v!1%nat) = (attester_id + ((2%F ^ 160%nat)%F * epoch)%F)%F)) /\ ((v!2%nat) = out1)) /\ ((length v) = 3%nat)) -> ((length v) = 3%nat)).
Proof. hammer. Qed.

Lemma StateTreeLeaf_obligation12: forall (FIELD_COUNT : nat) (data : (list F)) (identity_secret : F) (attester_id : F) (epoch : F) (out1 : F) (v : F), Forall (fun x14 => True) data -> ((length data) = FIELD_COUNT) -> True -> True -> True -> (out1 = (u_state_tree_leaf ((skipn 1%nat data)[:(FIELD_COUNT - 1%nat)%nat]) (data!0%nat))) -> True -> ((v = (Poseidon 3%nat (identity_secret :: ((attester_id + ((2%F ^ 160%nat)%F * epoch)%F)%F :: (out1 :: nil))))) -> (v = (Poseidon 3%nat (identity_secret :: ((attester_id + ((2%F ^ 160%nat)%F * epoch)%F)%F :: ((u_state_tree_leaf (skipn 1%nat data) (data!0%nat)) :: nil)))))).
Proof.
  intros;subst.
  assert((data [1:]) [:length data - 1] = (data [1:])).
  { rewrite <- ListUtil.List.firstn_all.
    rewrite ListUtil.skipn_length;auto. }
  rewrite H0;auto.
Qed.

(* IdentitySecret *)
Lemma IdentitySecret_obligation0: forall (nullifier : F) (trapdoor : F) (v : Z), True -> True -> True -> ((v = 2%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma IdentitySecret_obligation1: forall (nullifier : F) (trapdoor : F) (v : (list F)), True -> True -> Forall (fun x0 => True) v -> True -> ((((True /\ ((v!0%nat) = nullifier)) /\ ((v!1%nat) = trapdoor)) /\ ((length v) = 2%nat)) -> ((length v) = 2%nat)).
Proof. hammer. Qed.

Lemma IdentitySecret_obligation2: forall (nullifier : F) (trapdoor : F) (v : F), True -> True -> True -> ((v = (Poseidon 2%nat (nullifier :: (trapdoor :: nil)))) -> (v = (Poseidon 2%nat (nullifier :: (trapdoor :: nil))))).
Proof. hammer. Qed.

(* IdentityCommitment *)

Lemma IdentityCommitment_obligation0_trivial: forall (nullifier : F) (trapdoor : F) (v : F), True -> True -> True -> ((v = nullifier) -> True).
Proof. hammer. Qed.

Lemma IdentityCommitment_obligation1_trivial: forall (nullifier : F) (trapdoor : F) (v : F), True -> True -> True -> ((v = trapdoor) -> True).
Proof. hammer. Qed.

Lemma IdentityCommitment_obligation2: forall (nullifier : F) (trapdoor : F) (v : F), True -> True -> True -> ((v = (Poseidon 2%nat (nullifier :: (trapdoor :: nil)))) -> (v = (Poseidon 2%nat (nullifier :: (trapdoor :: nil))))).
Proof. hammer. Qed.

Lemma IdentityCommitment_obligation3: forall (nullifier : F) (trapdoor : F) (v : Z), True -> True -> True -> ((v = 1%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma IdentityCommitment_obligation4: forall (nullifier : F) (trapdoor : F) (v : (list F)), True -> True -> Forall (fun x1 => True) v -> True -> (((True /\ ((v!0%nat) = (Poseidon 2%nat (nullifier :: (trapdoor :: nil))))) /\ ((length v) = 1%nat)) -> ((length v) = 1%nat)).
Proof. hammer. Qed.

Lemma IdentityCommitment_obligation5: forall (nullifier : F) (trapdoor : F) (v : F), True -> True -> True -> ((v = (Poseidon 1%nat ((Poseidon 2%nat (nullifier :: (trapdoor :: nil))) :: nil))) -> (v = (Poseidon 1%nat ((Poseidon 2%nat (nullifier :: (trapdoor :: nil))) :: nil)))).
Proof. hammer. Qed.

Lemma IdentityCommitment_obligation6_trivial: forall (nullifier : F) (trapdoor : F), True -> True -> (True -> True).
Proof. hammer. Qed.

(* UpperLessThan *)
Lemma UpperLessThan_obligation0: forall (n : nat) (in_ : (list F)) (v : Z), (n <= 254%nat) -> Forall (fun x0 => True) in_ -> ((length in_) = 2%nat) -> True -> ((v = 254%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation1_trivial: forall (n : nat) (in_ : (list F)) (v : F), (n <= 254%nat) -> Forall (fun x1 => True) in_ -> ((length in_) = 2%nat) -> True -> ((v = (in_!0%nat)) -> True).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation2: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (v : Z), (n <= 254%nat) -> Forall (fun x2 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> True -> ((v = 254%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation3_trivial: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (v : F), (n <= 254%nat) -> Forall (fun x4 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x5 => ((x5 = 0%F) \/ (x5 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> True -> ((v = (in_!1%nat)) -> True).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation4: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (v : (list F)), (n <= 254%nat) -> Forall (fun x6 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x7 => ((x7 = 0%F) \/ (x7 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x8 => ((x8 = 0%F) \/ (x8 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> Forall (fun x9 => ((x9 = 0%F) \/ (x9 = 1%F))) v -> True -> (((((as_le_f v) = (in_!0%nat)) /\ ((length v) = 254%nat)) /\ (v = bits_0)) -> ((length v) = 254%nat)).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation5_trivial: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (v : F), (n <= 254%nat) -> Forall (fun x10 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x11 => ((x11 = 0%F) \/ (x11 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x12 => ((x12 = 0%F) \/ (x12 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> True -> (((v = 0%F) \/ (v = 1%F)) -> True).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation6: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (v : (list F)), (n <= 254%nat) -> Forall (fun x13 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x14 => ((x14 = 0%F) \/ (x14 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x15 => ((x15 = 0%F) \/ (x15 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> Forall (fun x16 => ((x16 = 0%F) \/ (x16 = 1%F))) v -> True -> (((((as_le_f v) = (in_!1%nat)) /\ ((length v) = 254%nat)) /\ (v = bits_1)) -> ((length v) = 254%nat)).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation7_trivial: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (v : F), (n <= 254%nat) -> Forall (fun x17 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x18 => ((x18 = 0%F) \/ (x18 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x19 => ((x19 = 0%F) \/ (x19 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> True -> (((v = 0%F) \/ (v = 1%F)) -> True).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation8: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (v : Z), (n <= 254%nat) -> Forall (fun x20 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x21 => ((x21 = 0%F) \/ (x21 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x22 => ((x22 = 0%F) \/ (x22 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> True -> ((((0%nat <= v) /\ (v <= 254%nat)) /\ (v = n)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation9_trivial: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (v : Z), (n <= 254%nat) -> Forall (fun x23 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x24 => ((x24 = 0%F) \/ (x24 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x25 => ((x25 = 0%F) \/ (x25 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> True -> ((v = 254%nat) -> True).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation10_trivial: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (v : Z), (n <= 254%nat) -> Forall (fun x26 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x27 => ((x27 = 0%F) \/ (x27 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x28 => ((x28 = 0%F) \/ (x28 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> True -> ((((0%nat <= v) /\ (v <= 254%nat)) /\ (v = n)) -> True).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation11_trivial: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (v : Z), (n <= 254%nat) -> Forall (fun x29 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x30 => ((x30 = 0%F) \/ (x30 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x31 => ((x31 = 0%F) \/ (x31 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> True -> ((v = (254%nat - n)%nat) -> True).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation12: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (v : (list F)), (n <= 254%nat) -> Forall (fun x32 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x33 => ((x33 = 0%F) \/ (x33 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x34 => ((x34 = 0%F) \/ (x34 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> Forall (fun x35 => ((x35 = 0%F) \/ (x35 = 1%F))) v -> True -> (((v = (skipn (254%nat - n)%nat bits_0)) /\ ((length v) = ((length bits_0) - (254%nat - n)%nat)%nat)) -> ((length v) = n)).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation13: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (v : F), (n <= 254%nat) -> Forall (fun x36 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x37 => ((x37 = 0%F) \/ (x37 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x38 => ((x38 = 0%F) \/ (x38 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> True -> (((v = 0%F) \/ (v = 1%F)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation14: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (upper_bits_0 : F) (v : Z), (n <= 254%nat) -> Forall (fun x39 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x40 => ((x40 = 0%F) \/ (x40 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x41 => ((x41 = 0%F) \/ (x41 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (upper_bits_0 = (as_le_f (skipn (254%nat - n)%nat bits_0))) -> True -> ((((0%nat <= v) /\ (v <= 254%nat)) /\ (v = n)) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation15_trivial: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (upper_bits_0 : F) (v : Z), (n <= 254%nat) -> Forall (fun x42 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x43 => ((x43 = 0%F) \/ (x43 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x44 => ((x44 = 0%F) \/ (x44 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (upper_bits_0 = (as_le_f (skipn (254%nat - n)%nat bits_0))) -> True -> ((v = 254%nat) -> True).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation16_trivial: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (upper_bits_0 : F) (v : Z), (n <= 254%nat) -> Forall (fun x45 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x46 => ((x46 = 0%F) \/ (x46 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x47 => ((x47 = 0%F) \/ (x47 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (upper_bits_0 = (as_le_f (skipn (254%nat - n)%nat bits_0))) -> True -> ((((0%nat <= v) /\ (v <= 254%nat)) /\ (v = n)) -> True).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation17_trivial: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (upper_bits_0 : F) (v : Z), (n <= 254%nat) -> Forall (fun x48 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x49 => ((x49 = 0%F) \/ (x49 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x50 => ((x50 = 0%F) \/ (x50 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (upper_bits_0 = (as_le_f (skipn (254%nat - n)%nat bits_0))) -> True -> ((v = (254%nat - n)%nat) -> True).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation18: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (upper_bits_0 : F) (v : (list F)), (n <= 254%nat) -> Forall (fun x51 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x52 => ((x52 = 0%F) \/ (x52 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x53 => ((x53 = 0%F) \/ (x53 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (upper_bits_0 = (as_le_f (skipn (254%nat - n)%nat bits_0))) -> Forall (fun x54 => ((x54 = 0%F) \/ (x54 = 1%F))) v -> True -> (((v = (skipn (254%nat - n)%nat bits_0)) /\ ((length v) = ((length bits_0) - (254%nat - n)%nat)%nat)) -> ((length v) = n)).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation19: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (upper_bits_0 : F) (v : F), ((n <= 254%nat) /\ (252%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x55 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x56 => ((x56 = 0%F) \/ (x56 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x57 => ((x57 = 0%F) \/ (x57 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (upper_bits_0 = (as_le_f (skipn (254%nat - n)%nat bits_0))) -> True -> (((v = 0%F) \/ (v = 1%F)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation20: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (upper_bits_0 : F) (upper_bits_1 : F) (v : Z), ((n <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x58 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x59 => ((x59 = 0%F) \/ (x59 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x60 => ((x60 = 0%F) \/ (x60 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (upper_bits_0 = (as_le_f (skipn (254%nat - n)%nat bits_0))) -> (upper_bits_1 = (as_le_f (skipn (254%nat - n)%nat bits_0))) -> True -> ((((0%nat <= v) /\ ((v <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z))) /\ (v = n)) -> ((0%nat <= v) /\ (v <= (C.k - 1%nat)%Z))).
Proof. hammer. Qed.

Lemma UpperLessThan_obligation21: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (upper_bits_0 : F) (upper_bits_1 : F) (v : F), ((n <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x61 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x62 => ((x62 = 0%F) \/ (x62 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x63 => ((x63 = 0%F) \/ (x63 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (upper_bits_0 = (as_le_f (skipn (254%nat - n)%nat bits_0))) -> (upper_bits_1 = (as_le_f (skipn (254%nat - n)%nat bits_0))) -> True -> (((v = (as_le_f (skipn (254%nat - n)%nat bits_0))) /\ (v = upper_bits_0)) -> ((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z)).
Proof.
intros. intuition. subst. rewrite as_le_f_lt.
assert(length (bits_0 [254 - n:]) = n).
{ rewrite ListUtil.skipn_length;auto. }
rewrite H5. auto.
Qed.

Lemma UpperLessThan_obligation22: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (upper_bits_0 : F) (upper_bits_1 : F) (v : F), ((n <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x64 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x65 => ((x65 = 0%F) \/ (x65 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x66 => ((x66 = 0%F) \/ (x66 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (upper_bits_0 = (as_le_f (skipn (254%nat - n)%nat bits_0))) -> (upper_bits_1 = (as_le_f (skipn (254%nat - n)%nat bits_0))) -> True -> (((v = (as_le_f (skipn (254%nat - n)%nat bits_0))) /\ (v = upper_bits_1)) -> ((^ v) <= ((2%nat ^ n)%Z - 1%nat)%Z)).
Proof.
intros. intuition. subst. rewrite as_le_f_lt.
assert(length (bits_0 [254 - n:]) = n).
{ rewrite ListUtil.skipn_length;auto. }
rewrite H5. auto.
Qed.

Lemma UpperLessThan_obligation23: forall (n : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (upper_bits_0 : F) (upper_bits_1 : F) (lt : F) (v : F), ((n <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x67 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x68 => ((x68 = 0%F) \/ (x68 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x69 => ((x69 = 0%F) \/ (x69 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (upper_bits_0 = (as_le_f (skipn (254%nat - n)%nat bits_0))) -> (upper_bits_1 = (as_le_f (skipn (254%nat - n)%nat bits_1))) -> (((lt = 0%F) \/ (lt = 1%F)) /\ (((lt = 1%F) -> ((^ upper_bits_0) < (^ upper_bits_1))) /\ ((lt = 0%F) -> ~((^ upper_bits_0) < (^ upper_bits_1))))) -> True -> (((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> ((^ upper_bits_0) < (^ upper_bits_1))) /\ ((v = 0%F) -> ~((^ upper_bits_0) < (^ upper_bits_1))))) /\ (v = lt)) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (((^ (in_!0%nat)) / (2%nat ^ (254%nat - n)%nat)%Z)%Z < ((^ (in_!1%nat)) / (2%nat ^ (254%nat - n)%nat)%Z)%Z)) /\ ((v = 0%F) -> ~(((^ (in_!0%nat)) / (2%nat ^ (254%nat - n)%nat)%Z)%Z < ((^ (in_!1%nat)) / (2%nat ^ (254%nat - n)%nat)%Z)%Z))))).
Proof.
intros. intuition; subst.
- apply H19. erewrite as_le_f_to_le_f_skipn;eauto. 
  erewrite as_le_f_to_le_f_skipn;eauto. 
- erewrite <- as_le_f_to_le_f_skipn;eauto. 
  erewrite <- as_le_f_to_le_f_skipn;eauto.
Qed. 

(* ReplFieldEqual *)

Lemma ReplFieldEqual_obligation0: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (v : Z), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x0 => True) in_ -> ((length in_) = 2%nat) -> True -> ((v = 254%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation1_trivial: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (v : F), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x1 => True) in_ -> ((length in_) = 2%nat) -> True -> ((v = (in_!0%nat)) -> True).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation2: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (v : Z), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x2 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x3 => ((x3 = 0%F) \/ (x3 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> True -> ((v = 254%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation3_trivial: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (v : F), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x4 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x5 => ((x5 = 0%F) \/ (x5 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> True -> ((v = (in_!1%nat)) -> True).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation4: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (v : (list F)), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x6 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x7 => ((x7 = 0%F) \/ (x7 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x8 => ((x8 = 0%F) \/ (x8 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> Forall (fun x9 => ((x9 = 0%F) \/ (x9 = 1%F))) v -> True -> (((((as_le_f v) = (in_!0%nat)) /\ ((length v) = 254%nat)) /\ (v = bits_0)) -> ((length v) = 254%nat)).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation5_trivial: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (v : F), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x10 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x11 => ((x11 = 0%F) \/ (x11 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x12 => ((x12 = 0%F) \/ (x12 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> True -> (((v = 0%F) \/ (v = 1%F)) -> True).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation6: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (v : (list F)), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x13 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x14 => ((x14 = 0%F) \/ (x14 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x15 => ((x15 = 0%F) \/ (x15 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> Forall (fun x16 => ((x16 = 0%F) \/ (x16 = 1%F))) v -> True -> (((((as_le_f v) = (in_!1%nat)) /\ ((length v) = 254%nat)) /\ (v = bits_1)) -> ((length v) = 254%nat)).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation7_trivial: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (v : F), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x17 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x18 => ((x18 = 0%F) \/ (x18 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x19 => ((x19 = 0%F) \/ (x19 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> True -> (((v = 0%F) \/ (v = 1%F)) -> True).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation8_trivial: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (v : Z), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x20 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x21 => ((x21 = 0%F) \/ (x21 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x22 => ((x22 = 0%F) \/ (x22 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> True -> ((v = 254%nat) -> True).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation9_trivial: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (v : Z), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x23 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x24 => ((x24 = 0%F) \/ (x24 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x25 => ((x25 = 0%F) \/ (x25 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> True -> ((((0%nat <= v) /\ ((v <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z))) /\ (v = REPL_NONCE_BITS)) -> True).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation10: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (v : Z), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x26 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x27 => ((x27 = 0%F) \/ (x27 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x28 => ((x28 = 0%F) \/ (x28 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> True -> ((v = (254%nat - REPL_NONCE_BITS)%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation11_trivial: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (v : Z), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x29 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x30 => ((x30 = 0%F) \/ (x30 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x31 => ((x31 = 0%F) \/ (x31 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> True -> ((v = 254%nat) -> True).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation12_trivial: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (v : Z), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x32 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x33 => ((x33 = 0%F) \/ (x33 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x34 => ((x34 = 0%F) \/ (x34 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> True -> ((((0%nat <= v) /\ ((v <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z))) /\ (v = REPL_NONCE_BITS)) -> True).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation13_trivial: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (v : Z), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x35 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x36 => ((x36 = 0%F) \/ (x36 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x37 => ((x37 = 0%F) \/ (x37 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> True -> ((v = (254%nat - REPL_NONCE_BITS)%nat) -> True).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation14: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (v : (list F)), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x38 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x39 => ((x39 = 0%F) \/ (x39 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x40 => ((x40 = 0%F) \/ (x40 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> Forall (fun x41 => ((x41 = 0%F) \/ (x41 = 1%F))) v -> True -> (((v = (bits_0[:(254%nat - REPL_NONCE_BITS)%nat])) /\ ((length v) = (254%nat - REPL_NONCE_BITS)%nat)) -> ((length v) = (254%nat - REPL_NONCE_BITS)%nat)).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation15: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (v : F), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x42 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x43 => ((x43 = 0%F) \/ (x43 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x44 => ((x44 = 0%F) \/ (x44 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> True -> (((v = 0%F) \/ (v = 1%F)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation16_trivial: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (repl_bits_0 : F) (v : Z), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x45 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x46 => ((x46 = 0%F) \/ (x46 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x47 => ((x47 = 0%F) \/ (x47 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (repl_bits_0 = (as_le_f (bits_0[:(254%nat - REPL_NONCE_BITS)%nat]))) -> True -> ((v = 254%nat) -> True).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation17_trivial: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (repl_bits_0 : F) (v : Z), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x48 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x49 => ((x49 = 0%F) \/ (x49 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x50 => ((x50 = 0%F) \/ (x50 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (repl_bits_0 = (as_le_f (bits_0[:(254%nat - REPL_NONCE_BITS)%nat]))) -> True -> ((((0%nat <= v) /\ ((v <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z))) /\ (v = REPL_NONCE_BITS)) -> True).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation18: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (repl_bits_0 : F) (v : Z), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x51 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x52 => ((x52 = 0%F) \/ (x52 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x53 => ((x53 = 0%F) \/ (x53 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (repl_bits_0 = (as_le_f (bits_0[:(254%nat - REPL_NONCE_BITS)%nat]))) -> True -> ((v = (254%nat - REPL_NONCE_BITS)%nat) -> (0%nat <= v)).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation19_trivial: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (repl_bits_0 : F) (v : Z), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x54 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x55 => ((x55 = 0%F) \/ (x55 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x56 => ((x56 = 0%F) \/ (x56 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (repl_bits_0 = (as_le_f (bits_0[:(254%nat - REPL_NONCE_BITS)%nat]))) -> True -> ((v = 254%nat) -> True).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation20_trivial: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (repl_bits_0 : F) (v : Z), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x57 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x58 => ((x58 = 0%F) \/ (x58 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x59 => ((x59 = 0%F) \/ (x59 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (repl_bits_0 = (as_le_f (bits_0[:(254%nat - REPL_NONCE_BITS)%nat]))) -> True -> ((((0%nat <= v) /\ ((v <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z))) /\ (v = REPL_NONCE_BITS)) -> True).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation21_trivial: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (repl_bits_0 : F) (v : Z), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x60 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x61 => ((x61 = 0%F) \/ (x61 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x62 => ((x62 = 0%F) \/ (x62 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (repl_bits_0 = (as_le_f (bits_0[:(254%nat - REPL_NONCE_BITS)%nat]))) -> True -> ((v = (254%nat - REPL_NONCE_BITS)%nat) -> True).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation22: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (repl_bits_0 : F) (v : (list F)), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x63 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x64 => ((x64 = 0%F) \/ (x64 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x65 => ((x65 = 0%F) \/ (x65 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (repl_bits_0 = (as_le_f (bits_0[:(254%nat - REPL_NONCE_BITS)%nat]))) -> Forall (fun x66 => ((x66 = 0%F) \/ (x66 = 1%F))) v -> True -> (((v = (bits_1[:(254%nat - REPL_NONCE_BITS)%nat])) /\ ((length v) = (254%nat - REPL_NONCE_BITS)%nat)) -> ((length v) = (254%nat - REPL_NONCE_BITS)%nat)).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation23: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (repl_bits_0 : F) (v : F), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x67 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x68 => ((x68 = 0%F) \/ (x68 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x69 => ((x69 = 0%F) \/ (x69 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (repl_bits_0 = (as_le_f (bits_0[:(254%nat - REPL_NONCE_BITS)%nat]))) -> True -> (((v = 0%F) \/ (v = 1%F)) -> ((v = 0%F) \/ (v = 1%F))).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation24_trivial: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (repl_bits_0 : F) (repl_bits_1 : F) (v : F), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x70 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x71 => ((x71 = 0%F) \/ (x71 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x72 => ((x72 = 0%F) \/ (x72 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (repl_bits_0 = (as_le_f (bits_0[:(254%nat - REPL_NONCE_BITS)%nat]))) -> (repl_bits_1 = (as_le_f (bits_1[:(254%nat - REPL_NONCE_BITS)%nat]))) -> True -> (((v = (as_le_f (bits_0[:(254%nat - REPL_NONCE_BITS)%nat]))) /\ (v = repl_bits_0)) -> True).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation25_trivial: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (repl_bits_0 : F) (repl_bits_1 : F) (v : F), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x73 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x74 => ((x74 = 0%F) \/ (x74 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x75 => ((x75 = 0%F) \/ (x75 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (repl_bits_0 = (as_le_f (bits_0[:(254%nat - REPL_NONCE_BITS)%nat]))) -> (repl_bits_1 = (as_le_f (bits_1[:(254%nat - REPL_NONCE_BITS)%nat]))) -> True -> (((v = (as_le_f (bits_1[:(254%nat - REPL_NONCE_BITS)%nat]))) /\ (v = repl_bits_1)) -> True).
Proof. hammer. Qed.

Lemma ReplFieldEqual_obligation26: forall (REPL_NONCE_BITS : nat) (in_ : (list F)) (bits_0 : (list F)) (bits_1 : (list F)) (alias0 : unit) (alias1 : unit) (repl_bits_0 : F) (repl_bits_1 : F) (eq : F) (v : F), ((REPL_NONCE_BITS <= 254%nat) /\ (254%nat <= (C.k - 1%nat)%Z)) -> Forall (fun x76 => True) in_ -> ((length in_) = 2%nat) -> Forall (fun x77 => ((x77 = 0%F) \/ (x77 = 1%F))) bits_0 -> (((as_le_f bits_0) = (in_!0%nat)) /\ ((length bits_0) = 254%nat)) -> Forall (fun x78 => ((x78 = 0%F) \/ (x78 = 1%F))) bits_1 -> (((as_le_f bits_1) = (in_!1%nat)) /\ ((length bits_1) = 254%nat)) -> ((^ (as_le_f bits_0)) < C.q) -> ((^ (as_le_f bits_1)) < C.q) -> (repl_bits_0 = (as_le_f (bits_0[:(254%nat - REPL_NONCE_BITS)%nat]))) -> (repl_bits_1 = (as_le_f (bits_1[:(254%nat - REPL_NONCE_BITS)%nat]))) -> (((eq = 0%F) \/ (eq = 1%F)) /\ (((eq = 1%F) -> (repl_bits_0 = repl_bits_1)) /\ ((eq = 0%F) -> ~(repl_bits_0 = repl_bits_1)))) -> True -> (((((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (repl_bits_0 = repl_bits_1)) /\ ((v = 0%F) -> ~(repl_bits_0 = repl_bits_1)))) /\ (v = eq)) -> (((v = 0%F) \/ (v = 1%F)) /\ (((v = 1%F) -> (((^ (in_!0%nat)) mod (2%nat ^ (254%nat - REPL_NONCE_BITS)%nat)%Z)%Z = ((^ (in_!1%nat)) mod (2%nat ^ (254%nat - REPL_NONCE_BITS)%nat)%Z)%Z)) /\ ((v = 0%F) -> ~(((^ (in_!0%nat)) mod (2%nat ^ (254%nat - REPL_NONCE_BITS)%nat)%Z)%Z = ((^ (in_!1%nat)) mod (2%nat ^ (254%nat - REPL_NONCE_BITS)%nat)%Z)%Z))))).
Proof.
intros. intuition; subst.
- apply H19. apply F.eq_to_Z_iff. 
  erewrite as_le_f_to_le_f_taken;eauto. 
  erewrite as_le_f_to_le_f_taken;eauto. 
- erewrite <- as_le_f_to_le_f_taken. 2: apply H. 
  erewrite <- as_le_f_to_le_f_taken. 2: apply H3.
  apply F.eq_to_Z_iff;auto.
Qed.