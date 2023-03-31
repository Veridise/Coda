(** * DSL benchmark: Bitify *)

(** ** Num2Bits *)

(* print_endline (generate_lemmas num2bits (typecheck_circuit d_empty num2bits));; *)

Lemma Num2Bits_obligation0: forall (n : nat) (_in : F) (v : Z), True -> True -> ((v = 0%nat) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation1: forall (n : nat) (_in : F) (v : Z), True -> True -> (((0%nat <= v) /\ (v = n)) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation2: forall (n : nat) (_in : F) (v : Z), True -> True -> (((0%nat <= v) /\ (v < n)) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation3: forall (n : nat) (_in : F) (i : nat) (v : (list F)), True -> (i < n) -> Forall (fun x0 => True) v -> True -> (((length v) = i) -> ((length v) = i)).
Proof. Admitted.

Lemma Num2Bits_obligation4: forall (n : nat) (_in : F) (i : nat) (x : (list F)) (star : F) (v : F), True -> (i < n) -> Forall (fun x1 => True) x -> ((length x) = i) -> True -> True -> ((v = star) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation5: forall (n : nat) (_in : F) (i : nat) (x : (list F)) (star : F) (v : (list F)), True -> (i < n) -> Forall (fun x2 => True) x -> ((length x) = i) -> True -> Forall (fun x3 => True) v -> True -> ((((length v) = i) /\ (v = x)) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation6: forall (n : nat) (_in : F) (i : nat) (x : (list F)) (star : F) (v : F), True -> (i < n) -> Forall (fun x4 => True) x -> ((length x) = i) -> True -> True -> (True -> True).
Proof. Admitted.

Lemma Num2Bits_obligation7: forall (n : nat) (_in : F) (i : nat) (x : (list F)) (star : F) (v : (list F)), True -> (i < n) -> Forall (fun x5 => True) x -> ((length x) = i) -> True -> Forall (fun x6 => True) v -> True -> ((v = (star :: x)) -> ((length v) = (i + 1%nat)%nat)).
Proof. Admitted.

Lemma Num2Bits_obligation8: forall (n : nat) (_in : F) (i : nat) (x : (list F)) (star : F) (v : F), True -> (i < n) -> Forall (fun x7 => True) x -> ((length x) = i) -> True -> True -> (True -> True).
Proof. Admitted.

Lemma Num2Bits_obligation9: forall (n : nat) (_in : F), True -> (((length v) = 0%nat) -> ((length v) = 0%nat)).
Proof. Admitted.

Lemma Num2Bits_obligation10: forall (n : nat) (_in : F) (out : (list F)) (v : Z), True -> Forall (fun x8 => True) out -> ((length out) = n) -> True -> ((v = 0%nat) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation11: forall (n : nat) (_in : F) (out : (list F)) (v : Z), True -> Forall (fun x9 => True) out -> ((length out) = n) -> True -> (((0%nat <= v) /\ (v = n)) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation12: forall (n : nat) (_in : F) (out : (list F)) (v : Z), True -> Forall (fun x10 => True) out -> ((length out) = n) -> True -> (((0%nat <= v) /\ (v < n)) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation13: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (v : F), True -> Forall (fun x11 => True) out -> ((length out) = n) -> (i < n) -> True -> ((v = (as_le_f (out[:i]))) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation14: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (v : F), True -> Forall (fun x12 => True) out -> ((length out) = n) -> (i < n) -> True -> ((v = (2%F ^ i)%F) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation15: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x13 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x14,x15) => (x14 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x14,x15) => (x15 = (2%F ^ i)%F) end -> match lc1_e2 with (x14,x15) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (as_le_f (out[:i]))) /\ (v = lc1)) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation16: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x16 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x17,x18) => (x17 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x17,x18) => (x18 = (2%F ^ i)%F) end -> match lc1_e2 with (x17,x18) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = (out!i)) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation17: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x19 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x20,x21) => (x20 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x20,x21) => (x21 = (2%F ^ i)%F) end -> match lc1_e2 with (x20,x21) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (2%F ^ i)%F) /\ (v = e2)) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation18: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x22 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x23,x24) => (x23 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x23,x24) => (x24 = (2%F ^ i)%F) end -> match lc1_e2 with (x23,x24) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = ((out!i) * e2)%F) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation19: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x25 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x26,x27) => (x26 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x26,x27) => (x27 = (2%F ^ i)%F) end -> match lc1_e2 with (x26,x27) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (2%F ^ i)%F) /\ (v = e2)) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation20: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x28 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x29,x30) => (x29 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x29,x30) => (x30 = (2%F ^ i)%F) end -> match lc1_e2 with (x29,x30) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (2%F ^ i)%F) /\ (v = e2)) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation21: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F * F), True -> Forall (fun x31 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x32,x33) => (x32 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x32,x33) => (x33 = (2%F ^ i)%F) end -> match lc1_e2 with (x32,x33) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> match v with (x34,x35) => (x34 = (lc1 + ((out!i) * e2)%F)%F) end -> match v with (x34,x35) => (x35 = (e2 + e2)%F) end -> match v with (x34,x35) => True end -> (True -> True).
Proof. Admitted.

Lemma Num2Bits_obligation22: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x36 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x37,x38) => (x37 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x37,x38) => (x38 = (2%F ^ i)%F) end -> match lc1_e2 with (x37,x38) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = (lc1 + ((out!i) * e2)%F)%F) -> (v = (as_le_f (out[:(i + 1%nat)%nat])))).
Proof. Admitted.

Lemma Num2Bits_obligation23: forall (n : nat) (_in : F) (out : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), True -> Forall (fun x39 => True) out -> ((length out) = n) -> (i < n) -> match lc1_e2 with (x40,x41) => (x40 = (as_le_f (out[:i]))) end -> match lc1_e2 with (x40,x41) => (x41 = (2%F ^ i)%F) end -> match lc1_e2 with (x40,x41) => True end -> (lc1 = (as_le_f (out[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = (e2 + e2)%F) -> (v = (2%F ^ (i + 1%nat)%nat)%F)).
Proof. Admitted.

Lemma Num2Bits_obligation24: forall (n : nat) (_in : F) (out : (list F)) (v : F), True -> Forall (fun x42 => True) out -> ((length out) = n) -> True -> ((v = 0%F) -> (v = (as_le_f (out[:0%nat])))).
Proof. Admitted.

Lemma Num2Bits_obligation25: forall (n : nat) (_in : F) (out : (list F)) (v : F), True -> Forall (fun x43 => True) out -> ((length out) = n) -> True -> ((v = 1%F) -> (v = (2%F ^ 0%nat)%F)).
Proof. Admitted.

Lemma Num2Bits_obligation26: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (v : Z), True -> Forall (fun x44 => True) out -> ((length out) = n) -> match lc1_e2 with (x45,x46) => (x45 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x45,x46) => (x46 = (2%F ^ n)%F) end -> match lc1_e2 with (x45,x46) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> True -> ((v = 0%nat) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation27: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (v : Z), True -> Forall (fun x47 => True) out -> ((length out) = n) -> match lc1_e2 with (x48,x49) => (x48 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x48,x49) => (x49 = (2%F ^ n)%F) end -> match lc1_e2 with (x48,x49) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> True -> (((0%nat <= v) /\ (v = n)) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation28: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (v : Z), True -> Forall (fun x50 => True) out -> ((length out) = n) -> match lc1_e2 with (x51,x52) => (x51 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x51,x52) => (x52 = (2%F ^ n)%F) end -> match lc1_e2 with (x51,x52) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> True -> (((0%nat <= v) /\ (v < n)) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation29: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (i : nat) (v : unit), True -> Forall (fun x53 => True) out -> ((length out) = n) -> match lc1_e2 with (x54,x55) => (x54 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x54,x55) => (x55 = (2%F ^ n)%F) end -> match lc1_e2 with (x54,x55) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (i < n) -> True -> ((forall (j:nat), 0%nat <= j < i -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation30: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (i : nat) (u : unit) (v : F), True -> Forall (fun x56 => True) out -> ((length out) = n) -> match lc1_e2 with (x57,x58) => (x57 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x57,x58) => (x58 = (2%F ^ n)%F) end -> match lc1_e2 with (x57,x58) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (i < n) -> (forall (j:nat), 0%nat <= j < i -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> True -> ((v = (out!i)) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation31: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (i : nat) (u : unit) (v : F), True -> Forall (fun x59 => True) out -> ((length out) = n) -> match lc1_e2 with (x60,x61) => (x60 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x60,x61) => (x61 = (2%F ^ n)%F) end -> match lc1_e2 with (x60,x61) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (i < n) -> (forall (j:nat), 0%nat <= j < i -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> True -> ((v = (out!i)) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation32: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (i : nat) (u : unit) (v : F), True -> Forall (fun x62 => True) out -> ((length out) = n) -> match lc1_e2 with (x63,x64) => (x63 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x63,x64) => (x64 = (2%F ^ n)%F) end -> match lc1_e2 with (x63,x64) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (i < n) -> (forall (j:nat), 0%nat <= j < i -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> True -> ((v = 1%F) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation33: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (i : nat) (u : unit) (v : F), True -> Forall (fun x65 => True) out -> ((length out) = n) -> match lc1_e2 with (x66,x67) => (x66 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x66,x67) => (x67 = (2%F ^ n)%F) end -> match lc1_e2 with (x66,x67) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (i < n) -> (forall (j:nat), 0%nat <= j < i -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> True -> ((v = ((out!i) - 1%F)%F) -> True).
Proof. Admitted.

Lemma Num2Bits_obligation34: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (i : nat) (u : unit) (v : unit), True -> Forall (fun x68 => True) out -> ((length out) = n) -> match lc1_e2 with (x69,x70) => (x69 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x69,x70) => (x70 = (2%F ^ n)%F) end -> match lc1_e2 with (x69,x70) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (i < n) -> (forall (j:nat), 0%nat <= j < i -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> True -> ((((out!i) * ((out!i) - 1%F)%F)%F = 0%F) -> (forall (j:nat), 0%nat <= j < (i + 1%nat)%nat -> (((out!j) = 0%F) \/ ((out!j) = 1%F)))).
Proof. Admitted.

Lemma Num2Bits_obligation35: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (v : unit), True -> Forall (fun x71 => True) out -> ((length out) = n) -> match lc1_e2 with (x72,x73) => (x72 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x72,x73) => (x73 = (2%F ^ n)%F) end -> match lc1_e2 with (x72,x73) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> True -> (True -> (forall (j:nat), 0%nat <= j < 0%nat -> (((out!j) = 0%F) \/ ((out!j) = 1%F)))).
Proof. Admitted.

Lemma Num2Bits_obligation36: forall (n : nat) (_in : F) (out : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (u0 : unit) (u : unit) (v : (list F)), True -> Forall (fun x74 => True) out -> ((length out) = n) -> match lc1_e2 with (x75,x76) => (x75 = (as_le_f (out[:n]))) end -> match lc1_e2 with (x75,x76) => (x76 = (2%F ^ n)%F) end -> match lc1_e2 with (x75,x76) => True end -> (lc1 = (as_le_f (out[:n]))) -> (e2 = (2%F ^ n)%F) -> (_in = lc1) -> (forall (j:nat), 0%nat <= j < n -> (((out!j) = 0%F) \/ ((out!j) = 1%F))) -> Forall (fun x77 => True) v -> True -> ((((length v) = n) /\ (v = out)) -> (((as_le_f v) = _in) /\ (forall (i0:nat), 0%nat <= i0 < (length v) -> (((v!i0) = 0%F) \/ ((v!i0) = 1%F))))).
Proof. Admitted.

(** ** Bits2Num *)

(* print_endline (generate_lemmas bits2num (typecheck_circuit d_empty bits2num));; *)

Lemma Bits2Num_obligation0: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x78 => ((x78 = 0%F) \/ (x78 = 1%F))) _in -> ((length _in) = n) -> True -> ((v = 0%nat) -> True).
Proof. Admitted.

Lemma Bits2Num_obligation1: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x79 => ((x79 = 0%F) \/ (x79 = 1%F))) _in -> ((length _in) = n) -> True -> (((0%nat <= v) /\ (v = n)) -> True).
Proof. Admitted.

Lemma Bits2Num_obligation2: forall (n : nat) (_in : (list F)) (v : Z), Forall (fun x80 => ((x80 = 0%F) \/ (x80 = 1%F))) _in -> ((length _in) = n) -> True -> (((0%nat <= v) /\ (v < n)) -> True).
Proof. Admitted.

Lemma Bits2Num_obligation3: forall (n : nat) (_in : (list F)) (i : nat) (v : F), Forall (fun x81 => ((x81 = 0%F) \/ (x81 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> True -> ((v = (as_le_f (_in[:i]))) -> True).
Proof. Admitted.

Lemma Bits2Num_obligation4: forall (n : nat) (_in : (list F)) (i : nat) (v : F), Forall (fun x82 => ((x82 = 0%F) \/ (x82 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> True -> ((v = (2%F ^ i)%F) -> True).
Proof. Admitted.

Lemma Bits2Num_obligation5: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), Forall (fun x83 => ((x83 = 0%F) \/ (x83 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x84,x85) => (x84 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x84,x85) => (x85 = (2%F ^ i)%F) end -> match lc1_e2 with (x84,x85) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (as_le_f (_in[:i]))) /\ (v = lc1)) -> True).
Proof. Admitted.

Lemma Bits2Num_obligation6: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), Forall (fun x86 => ((x86 = 0%F) \/ (x86 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x87,x88) => (x87 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x87,x88) => (x88 = (2%F ^ i)%F) end -> match lc1_e2 with (x87,x88) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = (_in!i)) -> True).
Proof. Admitted.

Lemma Bits2Num_obligation7: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), Forall (fun x89 => ((x89 = 0%F) \/ (x89 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x90,x91) => (x90 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x90,x91) => (x91 = (2%F ^ i)%F) end -> match lc1_e2 with (x90,x91) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (2%F ^ i)%F) /\ (v = e2)) -> True).
Proof. Admitted.

Lemma Bits2Num_obligation8: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), Forall (fun x92 => ((x92 = 0%F) \/ (x92 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x93,x94) => (x93 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x93,x94) => (x94 = (2%F ^ i)%F) end -> match lc1_e2 with (x93,x94) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = ((_in!i) * e2)%F) -> True).
Proof. Admitted.

Lemma Bits2Num_obligation9: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), Forall (fun x95 => ((x95 = 0%F) \/ (x95 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x96,x97) => (x96 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x96,x97) => (x97 = (2%F ^ i)%F) end -> match lc1_e2 with (x96,x97) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (2%F ^ i)%F) /\ (v = e2)) -> True).
Proof. Admitted.

Lemma Bits2Num_obligation10: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), Forall (fun x98 => ((x98 = 0%F) \/ (x98 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x99,x100) => (x99 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x99,x100) => (x100 = (2%F ^ i)%F) end -> match lc1_e2 with (x99,x100) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> (((v = (2%F ^ i)%F) /\ (v = e2)) -> True).
Proof. Admitted.

Lemma Bits2Num_obligation11: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F * F), Forall (fun x101 => ((x101 = 0%F) \/ (x101 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x102,x103) => (x102 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x102,x103) => (x103 = (2%F ^ i)%F) end -> match lc1_e2 with (x102,x103) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> match v with (x104,x105) => (x104 = (lc1 + ((_in!i) * e2)%F)%F) end -> match v with (x104,x105) => (x105 = (e2 + e2)%F) end -> match v with (x104,x105) => True end -> (True -> True).
Proof. Admitted.

Lemma Bits2Num_obligation12: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), Forall (fun x106 => ((x106 = 0%F) \/ (x106 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x107,x108) => (x107 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x107,x108) => (x108 = (2%F ^ i)%F) end -> match lc1_e2 with (x107,x108) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = (lc1 + ((_in!i) * e2)%F)%F) -> (v = (as_le_f (_in[:(i + 1%nat)%nat])))).
Proof. Admitted.

Lemma Bits2Num_obligation13: forall (n : nat) (_in : (list F)) (i : nat) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), Forall (fun x109 => ((x109 = 0%F) \/ (x109 = 1%F))) _in -> ((length _in) = n) -> (i < n) -> match lc1_e2 with (x110,x111) => (x110 = (as_le_f (_in[:i]))) end -> match lc1_e2 with (x110,x111) => (x111 = (2%F ^ i)%F) end -> match lc1_e2 with (x110,x111) => True end -> (lc1 = (as_le_f (_in[:i]))) -> (e2 = (2%F ^ i)%F) -> True -> ((v = (e2 + e2)%F) -> (v = (2%F ^ (i + 1%nat)%nat)%F)).
Proof. Admitted.

Lemma Bits2Num_obligation14: forall (n : nat) (_in : (list F)) (v : F), Forall (fun x112 => ((x112 = 0%F) \/ (x112 = 1%F))) _in -> ((length _in) = n) -> True -> ((v = 0%F) -> (v = (as_le_f (_in[:0%nat])))).
Proof. Admitted.

Lemma Bits2Num_obligation15: forall (n : nat) (_in : (list F)) (v : F), Forall (fun x113 => ((x113 = 0%F) \/ (x113 = 1%F))) _in -> ((length _in) = n) -> True -> ((v = 1%F) -> (v = (2%F ^ 0%nat)%F)).
Proof. Admitted.

Lemma Bits2Num_obligation16: forall (n : nat) (_in : (list F)) (lc1_e2 : F * F) (lc1 : F) (e2 : F) (v : F), Forall (fun x114 => ((x114 = 0%F) \/ (x114 = 1%F))) _in -> ((length _in) = n) -> match lc1_e2 with (x115,x116) => (x115 = (as_le_f (_in[:n]))) end -> match lc1_e2 with (x115,x116) => (x116 = (2%F ^ n)%F) end -> match lc1_e2 with (x115,x116) => True end -> (lc1 = (as_le_f (_in[:n]))) -> (e2 = (2%F ^ n)%F) -> True -> (((v = (as_le_f (_in[:n]))) /\ (v = lc1)) -> (v = (as_le_f _in))).
Proof. Admitted.
