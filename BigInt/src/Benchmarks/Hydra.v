(** * DSL benchmark: Hydra-S1 ZKPS *)

(** ** PositionSwitcher *)

(* print_endline (generate_lemmas position_switcher (typecheck_circuit d_empty position_switcher));; *)

Lemma PositionSwitcher_obligation0_trivial: forall (_in : (list F)) (s : F) (v : F), Forall (fun x0 => True) _in -> ((length _in) = 2%nat) -> True -> True -> ((v = s) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation1_trivial: forall (_in : (list F)) (s : F) (v : F), Forall (fun x1 => True) _in -> ((length _in) = 2%nat) -> True -> True -> ((v = 1%F) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation2_trivial: forall (_in : (list F)) (s : F) (v : F), Forall (fun x2 => True) _in -> ((length _in) = 2%nat) -> True -> True -> ((v = s) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation3_trivial: forall (_in : (list F)) (s : F) (v : F), Forall (fun x3 => True) _in -> ((length _in) = 2%nat) -> True -> True -> ((v = (1%F - s)%F) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation4_trivial: forall (_in : (list F)) (s : F) (_ : unit) (in0 : F) (in1 : F) (v : F), Forall (fun x4 => True) _in -> ((length _in) = 2%nat) -> True -> ((s * (1%F - s)%F)%F = 0%F) -> (in0 = (_in!0%nat)) -> (in1 = (_in!1%nat)) -> True -> (((v = (_in!1%nat)) /\ (v = in1)) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation5_trivial: forall (_in : (list F)) (s : F) (_ : unit) (in0 : F) (in1 : F) (v : F), Forall (fun x5 => True) _in -> ((length _in) = 2%nat) -> True -> ((s * (1%F - s)%F)%F = 0%F) -> (in0 = (_in!0%nat)) -> (in1 = (_in!1%nat)) -> True -> (((v = (_in!0%nat)) /\ (v = in0)) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation6_trivial: forall (_in : (list F)) (s : F) (_ : unit) (in0 : F) (in1 : F) (v : F), Forall (fun x6 => True) _in -> ((length _in) = 2%nat) -> True -> ((s * (1%F - s)%F)%F = 0%F) -> (in0 = (_in!0%nat)) -> (in1 = (_in!1%nat)) -> True -> ((v = (in1 - in0)%F) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation7_trivial: forall (_in : (list F)) (s : F) (_ : unit) (in0 : F) (in1 : F) (v : F), Forall (fun x7 => True) _in -> ((length _in) = 2%nat) -> True -> ((s * (1%F - s)%F)%F = 0%F) -> (in0 = (_in!0%nat)) -> (in1 = (_in!1%nat)) -> True -> ((v = s) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation8_trivial: forall (_in : (list F)) (s : F) (_ : unit) (in0 : F) (in1 : F) (v : F), Forall (fun x8 => True) _in -> ((length _in) = 2%nat) -> True -> ((s * (1%F - s)%F)%F = 0%F) -> (in0 = (_in!0%nat)) -> (in1 = (_in!1%nat)) -> True -> ((v = ((in1 - in0)%F * s)%F) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation9_trivial: forall (_in : (list F)) (s : F) (_ : unit) (in0 : F) (in1 : F) (v : F), Forall (fun x9 => True) _in -> ((length _in) = 2%nat) -> True -> ((s * (1%F - s)%F)%F = 0%F) -> (in0 = (_in!0%nat)) -> (in1 = (_in!1%nat)) -> True -> (((v = (_in!0%nat)) /\ (v = in0)) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation10_trivial: forall (_in : (list F)) (s : F) (_ : unit) (in0 : F) (in1 : F) (out0 : F) (v : F), Forall (fun x10 => True) _in -> ((length _in) = 2%nat) -> True -> ((s * (1%F - s)%F)%F = 0%F) -> (in0 = (_in!0%nat)) -> (in1 = (_in!1%nat)) -> (out0 = (((in1 - in0)%F * s)%F + in0)%F) -> True -> (((v = (_in!0%nat)) /\ (v = in0)) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation11_trivial: forall (_in : (list F)) (s : F) (_ : unit) (in0 : F) (in1 : F) (out0 : F) (v : F), Forall (fun x11 => True) _in -> ((length _in) = 2%nat) -> True -> ((s * (1%F - s)%F)%F = 0%F) -> (in0 = (_in!0%nat)) -> (in1 = (_in!1%nat)) -> (out0 = (((in1 - in0)%F * s)%F + in0)%F) -> True -> (((v = (_in!1%nat)) /\ (v = in1)) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation12_trivial: forall (_in : (list F)) (s : F) (_ : unit) (in0 : F) (in1 : F) (out0 : F) (v : F), Forall (fun x12 => True) _in -> ((length _in) = 2%nat) -> True -> ((s * (1%F - s)%F)%F = 0%F) -> (in0 = (_in!0%nat)) -> (in1 = (_in!1%nat)) -> (out0 = (((in1 - in0)%F * s)%F + in0)%F) -> True -> ((v = (in0 - in1)%F) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation13_trivial: forall (_in : (list F)) (s : F) (_ : unit) (in0 : F) (in1 : F) (out0 : F) (v : F), Forall (fun x13 => True) _in -> ((length _in) = 2%nat) -> True -> ((s * (1%F - s)%F)%F = 0%F) -> (in0 = (_in!0%nat)) -> (in1 = (_in!1%nat)) -> (out0 = (((in1 - in0)%F * s)%F + in0)%F) -> True -> ((v = s) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation14_trivial: forall (_in : (list F)) (s : F) (_ : unit) (in0 : F) (in1 : F) (out0 : F) (v : F), Forall (fun x14 => True) _in -> ((length _in) = 2%nat) -> True -> ((s * (1%F - s)%F)%F = 0%F) -> (in0 = (_in!0%nat)) -> (in1 = (_in!1%nat)) -> (out0 = (((in1 - in0)%F * s)%F + in0)%F) -> True -> ((v = ((in0 - in1)%F * s)%F) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation15_trivial: forall (_in : (list F)) (s : F) (_ : unit) (in0 : F) (in1 : F) (out0 : F) (v : F), Forall (fun x15 => True) _in -> ((length _in) = 2%nat) -> True -> ((s * (1%F - s)%F)%F = 0%F) -> (in0 = (_in!0%nat)) -> (in1 = (_in!1%nat)) -> (out0 = (((in1 - in0)%F * s)%F + in0)%F) -> True -> (((v = (_in!1%nat)) /\ (v = in1)) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation16_trivial: forall (_in : (list F)) (s : F) (_ : unit) (in0 : F) (in1 : F) (out0 : F) (out1 : F) (v : F), Forall (fun x16 => True) _in -> ((length _in) = 2%nat) -> True -> ((s * (1%F - s)%F)%F = 0%F) -> (in0 = (_in!0%nat)) -> (in1 = (_in!1%nat)) -> (out0 = (((in1 - in0)%F * s)%F + in0)%F) -> (out1 = (((in0 - in1)%F * s)%F + in1)%F) -> True -> (((v = (((in1 - in0)%F * s)%F + in0)%F) /\ (v = out0)) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation17_trivial: forall (_in : (list F)) (s : F) (_ : unit) (in0 : F) (in1 : F) (out0 : F) (out1 : F) (v : F), Forall (fun x17 => True) _in -> ((length _in) = 2%nat) -> True -> ((s * (1%F - s)%F)%F = 0%F) -> (in0 = (_in!0%nat)) -> (in1 = (_in!1%nat)) -> (out0 = (((in1 - in0)%F * s)%F + in0)%F) -> (out1 = (((in0 - in1)%F * s)%F + in1)%F) -> True -> (((v = (((in0 - in1)%F * s)%F + in1)%F) /\ (v = out1)) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation18_trivial: forall (_in : (list F)) (s : F) (_ : unit) (in0 : F) (in1 : F) (out0 : F) (out1 : F), Forall (fun x18 => True) _in -> ((length _in) = 2%nat) -> True -> ((s * (1%F - s)%F)%F = 0%F) -> (in0 = (_in!0%nat)) -> (in1 = (_in!1%nat)) -> (out0 = (((in1 - in0)%F * s)%F + in0)%F) -> (out1 = (((in0 - in1)%F * s)%F + in1)%F) -> (((length v) = 0%nat) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation19_trivial: forall (_in : (list F)) (s : F) (_ : unit) (in0 : F) (in1 : F) (out0 : F) (out1 : F) (v : (list F)), Forall (fun x19 => True) _in -> ((length _in) = 2%nat) -> True -> ((s * (1%F - s)%F)%F = 0%F) -> (in0 = (_in!0%nat)) -> (in1 = (_in!1%nat)) -> (out0 = (((in1 - in0)%F * s)%F + in0)%F) -> (out1 = (((in0 - in1)%F * s)%F + in1)%F) -> Forall (fun x20 => True) v -> True -> ((v = (out1 :: nil)) -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation20_trivial: forall (_in : (list F)) (s : F) (_ : unit) (in0 : F) (in1 : F) (out0 : F) (out1 : F) (v : F), Forall (fun x21 => True) _in -> ((length _in) = 2%nat) -> True -> ((s * (1%F - s)%F)%F = 0%F) -> (in0 = (_in!0%nat)) -> (in1 = (_in!1%nat)) -> (out0 = (((in1 - in0)%F * s)%F + in0)%F) -> (out1 = (((in0 - in1)%F * s)%F + in1)%F) -> True -> (True -> True).
Proof. intuit. Qed.

Lemma PositionSwitcher_obligation21: forall (_in : (list F)) (s : F) (_ : unit) (in0 : F) (in1 : F) (out0 : F) (out1 : F) (v : (list F)), Forall (fun x22 => True) _in -> ((length _in) = 2%nat) -> True -> ((s * (1%F - s)%F)%F = 0%F) -> (in0 = (_in!0%nat)) -> (in1 = (_in!1%nat)) -> (out0 = (((in1 - in0)%F * s)%F + in0)%F) -> (out1 = (((in0 - in1)%F * s)%F + in1)%F) -> Forall (fun x23 => True) v -> True -> ((v = (out0 :: (out1 :: nil))) -> ((((s = 0%F) \/ (s = 1%F)) -> (((s = 0%F) \/ (s = 1%F)) /\ (((s = 1%F) -> (((2%nat <= (length _in)) /\ (2%nat <= (length v))) /\ (((v!0%nat) = (_in!1%nat)) /\ ((v!1%nat) = (_in!0%nat))))) /\ ((s = 0%F) -> (((2%nat <= (length _in)) /\ (2%nat <= (length v))) /\ (((v!0%nat) = (_in!0%nat)) /\ ((v!1%nat) = (_in!1%nat)))))))) /\ ((length v) = 2%nat))).
Proof. Admitted.

Lemma PositionSwitcher_obligation22_trivial: forall (_in : (list F)) (s : F) (_ : unit) (in0 : F) (in1 : F) (out0 : F) (out1 : F) (v : F), Forall (fun x24 => True) _in -> ((length _in) = 2%nat) -> True -> ((s * (1%F - s)%F)%F = 0%F) -> (in0 = (_in!0%nat)) -> (in1 = (_in!1%nat)) -> (out0 = (((in1 - in0)%F * s)%F + in0)%F) -> (out1 = (((in0 - in1)%F * s)%F + in1)%F) -> True -> (True -> True).
Proof. intuit. Qed.

(** ** VerifyMerklePath *)

(* print_endline (generate_lemmas vrfy_mrkl_path (typecheck_circuit (add_to_deltas d_empty [poseidon; position_switcher]) vrfy_mrkl_path));; *)

(* TODO *)

(** ** VerifyHydraCommitment *)

(* print_endline (generate_lemmas vrfy_hydra_commit (typecheck_circuit (add_to_deltas d_empty [poseidon; vrfy_eddsa_poseidon]) vrfy_hydra_commit));; *)

Lemma VerifyHydraCommitment_obligation0: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (v : Z), True -> True -> Forall (fun x25 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x26 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> True -> ((v = 1%nat) -> (0%nat <= v)).
Proof. Admitted.

Lemma VerifyHydraCommitment_obligation1_trivial: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (v : F), True -> True -> Forall (fun x27 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x28 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> True -> ((v = secret) -> True).
Proof. intuit. Qed.

Lemma VerifyHydraCommitment_obligation2_trivial: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)), True -> True -> Forall (fun x29 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x30 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> (((length v) = 0%nat) -> True).
Proof. intuit. Qed.

Lemma VerifyHydraCommitment_obligation3: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (v : (list F)), True -> True -> Forall (fun x31 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x32 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> Forall (fun x33 => True) v -> True -> ((v = (secret :: nil)) -> ((length v) = 1%nat)).
Proof. Admitted.

Lemma VerifyHydraCommitment_obligation4_trivial: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (v : F), True -> True -> Forall (fun x34 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x35 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> True -> (True -> True).
Proof. intuit. Qed.

Lemma VerifyHydraCommitment_obligation5: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (commitment : F) (v : Z), True -> True -> Forall (fun x36 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x37 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> (commitment = (Poseidon 1%nat (secret :: nil))) -> True -> ((v = 2%nat) -> (0%nat <= v)).
Proof. Admitted.

Lemma VerifyHydraCommitment_obligation6_trivial: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (commitment : F) (v : F), True -> True -> Forall (fun x38 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x39 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> (commitment = (Poseidon 1%nat (secret :: nil))) -> True -> ((v = address) -> True).
Proof. intuit. Qed.

Lemma VerifyHydraCommitment_obligation7_trivial: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (commitment : F) (v : F), True -> True -> Forall (fun x40 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x41 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> (commitment = (Poseidon 1%nat (secret :: nil))) -> True -> (((v = (Poseidon 1%nat (secret :: nil))) /\ (v = commitment)) -> True).
Proof. intuit. Qed.

Lemma VerifyHydraCommitment_obligation8_trivial: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (commitment : F), True -> True -> Forall (fun x42 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x43 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> (commitment = (Poseidon 1%nat (secret :: nil))) -> (((length v) = 0%nat) -> True).
Proof. intuit. Qed.

Lemma VerifyHydraCommitment_obligation9_trivial: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (commitment : F) (v : (list F)), True -> True -> Forall (fun x44 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x45 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> (commitment = (Poseidon 1%nat (secret :: nil))) -> Forall (fun x46 => True) v -> True -> ((v = (commitment :: nil)) -> True).
Proof. intuit. Qed.

Lemma VerifyHydraCommitment_obligation10_trivial: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (commitment : F) (v : F), True -> True -> Forall (fun x47 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x48 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> (commitment = (Poseidon 1%nat (secret :: nil))) -> True -> (True -> True).
Proof. intuit. Qed.

Lemma VerifyHydraCommitment_obligation11: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (commitment : F) (v : (list F)), True -> True -> Forall (fun x49 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x50 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> (commitment = (Poseidon 1%nat (secret :: nil))) -> Forall (fun x51 => True) v -> True -> ((v = (address :: (commitment :: nil))) -> ((length v) = 2%nat)).
Proof. Admitted.

Lemma VerifyHydraCommitment_obligation12_trivial: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (commitment : F) (v : F), True -> True -> Forall (fun x52 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x53 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> (commitment = (Poseidon 1%nat (secret :: nil))) -> True -> (True -> True).
Proof. intuit. Qed.

Lemma VerifyHydraCommitment_obligation13_trivial: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (commitment : F) (message : F) (v : F), True -> True -> Forall (fun x54 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x55 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> (commitment = (Poseidon 1%nat (secret :: nil))) -> (message = (Poseidon 2%nat (address :: (commitment :: nil)))) -> True -> ((v = 1%F) -> True).
Proof. intuit. Qed.

Lemma VerifyHydraCommitment_obligation14_trivial: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (commitment : F) (message : F) (v : F), True -> True -> Forall (fun x56 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x57 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> (commitment = (Poseidon 1%nat (secret :: nil))) -> (message = (Poseidon 2%nat (address :: (commitment :: nil)))) -> True -> ((v = (commitmentMapperPubKey!0%nat)) -> True).
Proof. intuit. Qed.

Lemma VerifyHydraCommitment_obligation15_trivial: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (commitment : F) (message : F) (v : F), True -> True -> Forall (fun x58 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x59 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> (commitment = (Poseidon 1%nat (secret :: nil))) -> (message = (Poseidon 2%nat (address :: (commitment :: nil)))) -> True -> ((v = (commitmentMapperPubKey!1%nat)) -> True).
Proof. intuit. Qed.

Lemma VerifyHydraCommitment_obligation16_trivial: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (commitment : F) (message : F) (v : F), True -> True -> Forall (fun x60 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x61 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> (commitment = (Poseidon 1%nat (secret :: nil))) -> (message = (Poseidon 2%nat (address :: (commitment :: nil)))) -> True -> ((v = (commitmentReceipt!2%nat)) -> True).
Proof. intuit. Qed.

Lemma VerifyHydraCommitment_obligation17_trivial: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (commitment : F) (message : F) (v : F), True -> True -> Forall (fun x62 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x63 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> (commitment = (Poseidon 1%nat (secret :: nil))) -> (message = (Poseidon 2%nat (address :: (commitment :: nil)))) -> True -> ((v = (commitmentReceipt!0%nat)) -> True).
Proof. intuit. Qed.

Lemma VerifyHydraCommitment_obligation18_trivial: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (commitment : F) (message : F) (v : F), True -> True -> Forall (fun x64 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x65 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> (commitment = (Poseidon 1%nat (secret :: nil))) -> (message = (Poseidon 2%nat (address :: (commitment :: nil)))) -> True -> ((v = (commitmentReceipt!1%nat)) -> True).
Proof. intuit. Qed.

Lemma VerifyHydraCommitment_obligation19_trivial: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (commitment : F) (message : F) (v : F), True -> True -> Forall (fun x66 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x67 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> (commitment = (Poseidon 1%nat (secret :: nil))) -> (message = (Poseidon 2%nat (address :: (commitment :: nil)))) -> True -> (((v = (Poseidon 2%nat (address :: (commitment :: nil)))) /\ (v = message)) -> True).
Proof. intuit. Qed.

Lemma VerifyHydraCommitment_obligation20_trivial: forall (address : F) (secret : F) (commitmentMapperPubKey : (list F)) (commitmentReceipt : (list F)) (commitment : F) (message : F) (v : unit), True -> True -> Forall (fun x68 => True) commitmentMapperPubKey -> ((length commitmentMapperPubKey) = 2%nat) -> Forall (fun x69 => True) commitmentReceipt -> ((length commitmentReceipt) = 3%nat) -> (commitment = (Poseidon 1%nat (secret :: nil))) -> (message = (Poseidon 2%nat (address :: (commitment :: nil)))) -> True -> (True -> True).
Proof. intuit. Qed.

(** ** hydraS1 *)

(* print_endline (generate_lemmas hydra_s1 (typecheck_circuit (add_to_deltas d_empty [num2bits; leq; poseidon; vrfy_hydra_commit; vrfy_mrkl_path]) hydra_s1));; *)

(* TODO *)
