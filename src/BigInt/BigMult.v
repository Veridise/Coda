Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Peano.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.PArith.BinPosDef.
Require Import Coq.ZArith.BinInt Coq.ZArith.ZArith Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.NArith.Nnat.

Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Field.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems Crypto.Arithmetic.PrimeFieldTheorems.

Require Import Circom.Tuple.
Require Import Crypto.Util.Decidable Crypto.Util.Notations.
Require Import BabyJubjub.
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Ring.

Require Import Util DSL.
Require Import Circom.circomlib.Bitify.

(* Require Import VST.zlist.Zlist. *)

Require Import Circom.Circom.
Require Import Circom.BigInt.Polynom.

(* Circuit:
* https://github.com/0xPARC/circom-ecdsa/blob/08c2c905b918b563c81a71086e493cb9d39c5a08/circuits/bigint.circom
*)


Module BigInt (C: CIRCOM).

Import C.

Local Open Scope list_scope.
Local Open Scope F_scope.
Local Open Scope P_scope.
Local Open Scope circom_scope.

(**************************
 * Overflow Representation
 **************************)


(* peel off 1 from x^(i+1) in field exp *)
Lemma pow_S_N: forall (x: F) i,
  x ^ (N.of_nat (S i)) = x * x ^ (N.of_nat i).
Proof.
  unwrap_C.
  intros.
  replace (N.of_nat (S i)) with (N.succ (N.of_nat i)).
  apply F.pow_succ_r.
  induction i.
  - reflexivity.
  - simpl. f_equal.
Qed.

(* peel off 1 from x^(i+1) in int exp *)
Lemma pow_S_Z: forall (x: Z) i,
  (x ^ (Z.of_nat (S i)) = x * x ^ (Z.of_nat i))%Z.
Proof.
  intros.
  replace (Z.of_nat (S i)) with (Z.of_nat i + 1)%Z by lia.
  rewrite Zpower_exp; lia.
Qed.




Definition polynomial := list F.

(* polynomial addition *)
Fixpoint pairwise {A: Type} (op: A -> A -> A) (p q: list A) : list A :=
  match p, q with
  | nil, q => q
  | p, nil => p
  | (c :: p), (d :: q) => (op c d) :: pairwise op p q
  end.

Definition padd : polynomial -> polynomial -> polynomial := pairwise F.add.

(* polynomial multiplication *)
Fixpoint pmul (xs ys: polynomial) : polynomial :=
  match xs with
  | nil => nil
  | (x :: xs') => padd (List.map (fun y => x * y) ys) (0 :: (pmul xs' ys))
  end.

(* polynomial evaluation *)
Fixpoint eval' (i: N) (cs: polynomial) (x: F) : F :=
  match cs with
  | nil => 0
  | c::cs' => c * x^i + eval' (i+1)%N cs' x
  end.

Definition eval := eval' 0.

Definition toPoly {m} (xs: tuple F m) : polynomial := to_list m xs.

Lemma toPoly_length: forall {m} (xs: tuple F m),
  length (toPoly xs) = m.
Proof.
  intros. apply length_to_list.
Qed.

Definition coeff (i: nat) (cs: polynomial) := nth i cs 0.

Lemma coeff_nth: forall {m} (xs: tuple F m) i,
  coeff i (toPoly xs) = nth_default 0 i xs.
Proof.
  unfold coeff. unfold toPoly. intros.
  rewrite <- nth_default_eq. apply nth_default_to_list.
Qed.

Lemma eval'_ppadd: forall c n d x, eval' n (padd c d) x = eval' n c x + eval' n d x.
Proof.
  unwrap_C.
  unfold padd.
  induction c; simpl;intros; try fqsatz.
  destruct d.
  - simpl. fqsatz.
  - simpl. rewrite IHc. fqsatz.
Qed.

Theorem eval_ppadd: forall c d x, eval (padd c d) x = eval c x + eval d x.
Proof.
  intros. apply eval'_ppadd.
Qed.

Lemma ppmul_nil_0: forall c, pmul c nil = (List.repeat 0 (length c)).
Proof.
  induction c;auto.
  unfold padd. simpl. rewrite IHc. auto.
Qed.

Lemma eval_repeat_0: forall k n x, eval' n (List.repeat 0 k) x = 0.
Admitted.

Lemma eval'_ppmul_inner:
  forall d a n x,
  eval' n (List.map (fun y : F => a * y) d) x = 
   a * eval' n d x.
Proof.
  unwrap_C. induction d;simpl;intros;try fqsatz.
  rewrite IHd. fqsatz.
Qed.

Lemma eval'_n_plus_1: forall c n x, eval' (n + 1) c x = x * eval' n c x.
Proof.
  unwrap_C. induction c; simpl;intros; try fqsatz. 
  rewrite IHc.
  assert(x * (a * x ^ n + eval' (n + 1) c x) = x * a * x ^ n + x * eval' (n + 1) c x) by
  fqsatz.
  rewrite H.
  assert(a * x ^ (n + 1) = x * a * x ^ n).
  assert(x * a * x ^ n = a * x * x ^ n) by fqsatz. rewrite H0.
  assert(x ^ (n + 1) =  x * x ^ n).
  rewrite <- F.pow_succ_r.
  assert(N.succ n = (n + 1) %N). lia. rewrite H1. fqsatz.
  rewrite H1. fqsatz. rewrite H0. fqsatz.
Qed.

Lemma eval'_n_plus_1_0: forall c x, eval' 1 c x = x * eval' 0 c x.
Proof.
  intros. rewrite <- eval'_n_plus_1. auto.
Qed.

Lemma eval'_ppmul: forall c d x, eval' 0 (pmul c d) x = eval' 0 c x * eval' 0 d x.
Proof.
  unwrap_C. induction c; simpl;intros; try fqsatz. 
  rewrite eval'_ppadd. simpl. repeat rewrite eval'_n_plus_1_0.
  rewrite IHc. rewrite eval'_ppmul_inner.
  rewrite F.pow_0_r. fqsatz.
Qed.

Lemma eval_ppmul: forall c d x, eval (pmul c d) x = eval c x * eval d x.
Proof.
  intros. apply eval'_ppmul.
Qed.

Lemma firstn_toPoly: forall m (x: tuple F m),
  firstn m (toPoly x) = toPoly x.
Proof.
  intros.
  apply firstn_all2. unfold toPoly.
  rewrite length_to_list;lia.
Qed.

Lemma eval_app': forall cs0 cs1 n x,
  eval' n (cs0 ++ cs1) x = eval' n cs0 x + eval' (n + N.of_nat (length cs0)) cs1 x.
Proof.
  unwrap_C. induction cs0;simpl;intros.
  - assert(n + 0 =n)%N by lia. rewrite H. fqsatz.
  - rewrite IHcs0.
    assert (N.pos (Pos.of_succ_nat (length cs0)) = (1 + N.of_nat (length cs0))%N).
    rewrite Pos.of_nat_succ. lia.
    rewrite H. 
    assert(n + (1 + N.of_nat (length cs0)) = n + 1 + N.of_nat (length cs0))%N. lia.
    rewrite H0. fqsatz.
Qed.

Lemma eval_app: forall cs0 cs1 x,
  eval (cs0 ++ cs1) x = eval cs0 x + eval' (N.of_nat (length cs0)) cs1 x.
Proof.
  intros. apply eval_app'.
Qed.


Local Notation "x [ i ]" := (Tuple.nth_default 0 i x).

Definition nth2 {m n} (i: nat) (x: tuple (tuple F n) m) := Tuple.nth_default (repeat 0 n) i x.
(* Local Notation "x [ i ][ j ]" := (Tuple.nth_default 0 j (nth2 i x)). *)

Module D := DSL C.

Definition init_poly ka kb (poly: tuple F (ka+ kb -1)) {m: nat} (x: tuple F m) _C := 
  D.iter (fun i _C => _C /\
        (* inner loop: poly[i] = \sum_{j=0...ka+kb-1} x[j] * i ** j *)
        poly[i] = D.iter (fun j poly_i =>
          (poly_i + x[j] * (F.of_nat q i)^(N.of_nat j))) m 0)
          (ka+kb-1)  _C.

Lemma exists_last': forall {A: Type} (l: list A),
  l <> nil ->
  exists l' a, l = l' ++ a::nil.
Proof.
  intros.
  pose proof exists_last as H_last.
  specialize (H_last _ _ H). destruct H_last as [l' H_last]. destruct H_last as [a H_last].
  eexists. eexists. eauto.
Qed.

(* Import Polynomial. *)

(* Print polynomial. *)

(* Definition x : F := 0. *)
(* Definition p : polynomial := @nil F. *)
(* Definition y : F := (1 + (peval x p)). *)
(* 
Variable m: nat.
Variable x: tuple F m.
Definition f := toPoly x.
Print f.
*)

Lemma init_poly_correct: forall {ka kb} (poly: tuple F (ka+ kb -1)) {m} (x: tuple F m) _C,
  init_poly ka kb poly x _C ->
  (_C (* output constraint preserves _C *)
  /\ forall i, (i < ka + kb -1)%nat -> 
    poly [i] = eval (toPoly x) (F.of_nat q i : F)).
Proof.
  unwrap_C. unfold init_poly.
  intros ka kb poly m x _C0.
  remember (ka+kb-1)%nat as outer_bound.
  (* invariant for the inner loop *)
  remember (fun (i : nat) (_C : Prop) =>
  _C /\
  poly [i] =
  D.iter
    (fun (j : nat) (poly_i : F) =>
     poly_i + x [j] * F.of_nat q i ^ N.of_nat j) m 0)
  as outer.
  
  pose (Inv_outer := fun i _C =>
    _C -> _C0 /\ forall i0, (i0 < i)%nat -> poly [i0] = eval (toPoly x) (F.of_nat q i0)).
  assert (Hinv_outer: Inv_outer outer_bound (D.iter outer outer_bound _C0)). {
    apply D.iter_inv; unfold Inv_outer.
    (* outer: base case *)
    - intuition idtac. lia.
    (* outer: inductive case *)
    - intros i0 C_prev Hprev H_i0_i.
      rewrite Heqouter.
      intros H_C_prev.
      intuition idtac.
      destruct (dec (i1 < i0)%nat).
      + apply H3. lia.
      + assert (i1 = i0) by lia. subst.
        pose (Inv_inner := fun j acc => acc = eval (firstn j (toPoly x)) (F.of_nat q i0)).
        remember (fun (j : nat) (poly_i : F) => poly_i + x [j] * F.of_nat q i0 ^ N.of_nat j)
          as inner.
        assert (Hinv_inner: Inv_inner m (D.iter inner m 0)). {
          apply D.iter_inv; unfold Inv_inner.
          - intuition idtac.
          - intros j acc Hacc H_j_m. subst.
            destruct m.
            + lia.
            + assert (H_toPoly_len: length (toPoly x) = S m) by apply toPoly_length.
              assert (H_split: exists cs c ds, toPoly x = cs ++ (c::nil) ++ ds /\ length cs = j). {
                (* TODO: simplify this monstrosity *)
                remember (toPoly x) as xs.
                assert (exists cs ds, xs = cs ++ ds /\ length cs = S j). {
                  exists (firstn (S j) xs). exists (skipn (S j) xs).
                  rewrite firstn_skipn. split; auto. apply firstn_length_le. lia.
                }
                destruct H4 as [cs H4]. destruct H4 as [ds H4]. destruct H4.
                assert (H_cs_nonil: cs <> nil). unfold not. intros. subst. simpl in *. lia.
                apply exists_last' in H_cs_nonil.
                destruct H_cs_nonil as [cs' Hcs]. destruct Hcs as [c Hcs].
                exists cs'. exists c. exists ds. rewrite H4. rewrite Hcs. split.
                - rewrite app_assoc. reflexivity.
                - assert (length cs = length (cs' ++ c :: nil)) by (subst; auto).
                  rewrite app_length in H6. simpl in H6. lia.
              }
              destruct H_split as [cs H_split]. destruct H_split as [c H_split]. destruct H_split as [cs' H_split]. destruct H_split as [H_split H_cs_len].
              rewrite H_split.
              (* TODO: simplify this monstrosity *)
              rewrite firstn_app. replace (j-length cs)%nat with 0%nat by lia. rewrite firstn_O. rewrite app_nil_r.
              replace (firstn j cs) with (firstn (length cs) cs) by (rewrite <- H_cs_len; reflexivity).
              rewrite firstn_all.
              replace (cs ++ (c :: nil) ++ cs') with ((cs ++ (c :: nil)) ++ cs') by (rewrite app_assoc; reflexivity).
              replace (S j) with (length (cs ++ c :: nil)) by (rewrite app_length; simpl; lia).
              rewrite firstn_app. rewrite firstn_all.
              replace (length (cs ++ c :: nil) - length (cs ++ c :: nil))%nat with 0%nat by lia.
              rewrite firstn_O. rewrite app_nil_r. rewrite eval_app. cbn [eval'].
              replace c with (x [j] ). subst. replace (length cs + 0)%nat with (length cs) by lia.
              fqsatz.
              rewrite <- coeff_nth. rewrite H_split.
              replace (cs ++ (c :: nil) ++ cs') with ((cs ++ (c :: nil)) ++ cs') by (rewrite app_assoc; reflexivity).
              unfold coeff. rewrite app_nth1. rewrite app_nth2. subst. replace (length cs - length cs)%nat with 0%nat by lia. reflexivity.
              lia.
              rewrite app_length. simpl. lia.
        }
        unfold Inv_inner in Hinv_inner.
        rewrite firstn_toPoly in Hinv_inner. 
        rewrite H0, Hinv_inner. reflexivity.
  }
  intros.
  unfold Inv_outer in Hinv_outer.
  intuition idtac.
Qed.

Definition BigMultNoCarry_cons
  ka kb
  (a: tuple F ka)
  (b: tuple F kb)
  (out: tuple F (ka + kb - 1))
  (a_poly: tuple F (ka+ kb -1))
  (b_poly: tuple F (ka+ kb -1))
  (out_poly: tuple F (ka+ kb -1)) 
  :=
  let _C := True in
  let _C :=
    init_poly ka kb out_poly out _C in
  let _C :=
    init_poly ka kb a_poly a _C in
  let _C :=
    init_poly ka kb b_poly b _C in
  let _C :=
    D.iter (fun i _C => _C /\ 
      out_poly[i] = a_poly[i] * b_poly[i] ) (ka+kb-1) _C in
  _C.

Declare Scope DSL_scope.
Delimit Scope DSL_scope with DSL.

Module DL := DSLL C.
Import DL.

Notation "a +d b" := (addL a b) (at level 50) : DSL_scope.
Notation "a *d b" := (mulL a b) (at level 40) : DSL_scope.
Notation "a $d b" := (scaleL a b) (at level 30) : DSL_scope.
Notation "a ==d b" := (eqL a b) (at level 60) : DSL_scope.

Local Open Scope DSL_scope.

Local Coercion N.of_nat: nat >-> N.
Local Coercion Z.of_nat: nat >-> Z.
Print init0.
Definition BigMultNoCarry_cons'
  ka kb
  (a: list F)
  (b: list F)
  (out: list F) 
  (Ha: length a = ka )
  (Hb: length b = kb )
  :=
  let k := (ka + kb - 1)%nat in
  length out = k /\
  let powers := init0 (fun i => init0 (fun j => (F.of_nat q i)^j) k) k in
  let poly := fun k x => init0 (fun i => sumL_F (x *d (List.nth i powers nil))) k in
  poly k out ==d poly ka a *d poly kb b.

Definition BigMultNoCarry
  ka kb
  (a: tuple F ka)
  (b: tuple F kb)
  (out: tuple F (ka + kb - 1)) :=
  exists a_poly b_poly out_poly,
    BigMultNoCarry_cons ka kb a b out a_poly b_poly out_poly.

(* Partial spec *)
Definition BigMultNoCarry_spec
  ka kb
  (a: tuple F ka)
  (b: tuple F kb)
  (out: tuple F (ka + kb -1)) :=
  to_list (ka + kb -1) out = pmul (to_list ka a) (to_list kb b).

(* Complete spec *)
(* to_list (ka + kb -1) out = mult (to_list ka (map toSZ a)) (to_list kb (map toSZ b)). *)

Fixpoint range (n: nat) : list nat :=
  match n with
  | O => nil
  | S n' => n' :: range n'
  end.
Lemma range_range: forall n i, In i (range n) -> (i < n)%nat.
Proof.
  induction n; simpl; intros; destruct H.
  - subst. lia.
  - assert (i < n)%nat by auto. lia.
Qed.
Lemma range_nodup: forall n, NoDup (range n).
Proof.
  induction n; simpl; constructor; auto.
  unfold not. intros. apply range_range in H. lia.
Qed.
Lemma range_elem: forall n i, (i < n)%nat -> In i (range n).
Proof.
  induction n; simpl; intros.
  - lia.
  - destruct (dec (i < n)%nat).
    + right. apply IHn. lia.
    + left. lia.
Qed.
Lemma range_P: forall P n,
  (forall i, (i < n)%nat -> P i) ->
  (forall i, In i (range n) -> P i).
Proof.
  intros. apply X. apply range_range. auto.
Qed.
Lemma range_length: forall n, length (range n) = n.
Proof. induction n; simpl; auto. Qed.
Lemma range_map_preimage {A: Type}: forall n (f: nat -> A) x,
  In x (List.map f (range n)) ->
  exists i, (i < n)%nat /\ f i = x.
Proof.
  induction n; simpl; intros; destruct H.
  - subst. exists n. split; (auto || lia).
  - apply IHn in H. inversion H. intuition idtac. exists x0. split; (auto || lia).
Qed.

Require Import FinFun.

Lemma Fof_Z_inj: forall x y, 0 <= x < q -> 0 <= y < q -> F.of_Z q x = F.of_Z q y -> x = y.
Proof.
  intros.
  apply F.eq_of_Z_iff in H1.
  rewrite Zmod_small in H1; rewrite Zmod_small in H1; lia.
Qed.

Lemma Fof_nat_injective: forall x y, Z.of_nat x < q -> Z.of_nat y < q -> F.of_nat q x = F.of_nat q y -> x = y.
Proof.
  intros. apply Nat2Z.inj. unfold F.of_nat in *. apply Fof_Z_inj; (lia || auto).
Qed.

Definition Injective_restrict {A B: Type} (f: A -> B) P :=
  forall x y, P x -> P y -> f x = f y -> x = y.

Lemma Injective_map_NoDup_restrict:
  forall (A B : Type) (f : A -> B) (l : list A) P,
  Injective_restrict f P -> (forall x, In x l -> P x) -> NoDup l -> NoDup (List.map f l).
Proof.
  induction l; simpl; intros; constructor.
  - unfold not. intros. apply in_map_iff in H1. destruct H1. intuition.
    apply H in H2.
    assert (~ (In a l)). replace l with (nil ++ l) by reflexivity. apply NoDup_remove_2. simpl. auto.
    subst. auto. apply X. auto.
    apply X. left. auto.
  - eapply IHl; eauto. inversion H0. auto.
Qed.

Definition degree := option nat.
Definition mk_degree (n: nat) := Some n.

Fixpoint deg (p: polynomial) : degree := 
  match p with
  | nil => None
  | a::p' =>
    match deg p' with
    | Some d => Some (S d)
    | None => if (F.eq_dec a 0) then None else Some O
    end
  end.

Definition degree_max d1 d2 :=
  match d1, d2 with
  | None, _ => d2
  | _, None => d1
  | Some d1, Some d2 => Some (max d1 d2)
  end.

Definition degree_leqb d1 d2 :=
  match d1, d2 with
  | Some d1, Some d2 => (d1 <=? d2)%nat
  | None, _ => true
  | _, None => false
  end.
Definition degree_leq d1 d2 : Prop := degree_leqb d1 d2 = true.

Definition pscale (k: F) : polynomial -> polynomial := List.map (fun a => k * a).
Definition psub (p q: polynomial) : polynomial := padd p (pscale (F.opp 1) q).

Lemma eval_popp': forall p0 n (x: F), 
eval' n (pscale (F.opp 1) p0) x = 0 - eval' n p0 x.
Proof.
  unwrap_C.
  unfold pscale. 
  induction p0; simpl;intros; try fqsatz.
  rewrite IHp0. fqsatz.
Qed.

Lemma eval_popp: forall p0 (x: F), 
eval (pscale (F.opp 1) p0) x = 0 - eval p0 x.
Proof.
  intros. apply eval_popp'.
Qed.

Lemma eval_psub: forall (p0 q0: polynomial) (x: F), (*11*)
  eval (psub p0 q0) x = eval p0 x - eval q0 x.
Proof.
  unwrap_C.
  unfold psub. intros. rewrite eval_ppadd. rewrite eval_popp. fqsatz.
Qed.

Lemma deg_psub: forall p q, (*11*)
  degree_leq (deg (psub p q)) (degree_max (deg p) (deg q)).
Proof.
Admitted.

Lemma eq_poly_decidable: forall p q : polynomial, (*11*)
  p = q \/ ~ (p = q).
Proof.
  intros p q. pose proof (dec_eq_list p q). destruct H;auto.
Qed.

Definition p0 : polynomial := nil.

Lemma psub_0_neg: forall p q, (*11*)
  ~((psub p q) = p0) <-> ~(p = q).
Proof.
Admitted.

Lemma not0_implies_positive_deg: forall p, (*11*)
  ~ (p = p0) -> exists n, deg p = Some n /\ (n > 0)%nat.
  Proof.
Admitted.

Definition root x p := eval p x = 0.

Lemma deg_d_has_most_d_roots: forall p d, (*11*)
  deg p = Some d ->
  (d > 0)%nat ->
  exists X, length X = d /\ forall x, root x p -> In x X.
Proof.
Admitted.


Lemma degree_leq_trans: forall a b d n,
  degree_leq a (Some n) ->
  degree_leq b (Some n) ->
  degree_leq (Some d) (degree_max a b) ->
  (d <= n)%nat.
Proof.
Admitted.

Theorem interpolant_unique: forall (a b: polynomial) n (X: list F),
  degree_leq (deg a) (Some n) ->
  degree_leq (deg b) (Some n) ->
  (length X > n)%nat ->
  NoDup X ->
  (forall x, In x X -> eval a x = eval b x) ->
  a = b.
Proof.
  (* Proof: https://inst.eecs.berkeley.edu/~cs70/fa14/notes/n7.pdf *)
  unwrap_C.
  intros.
  destruct (eq_poly_decidable a b).
  trivial.
  exfalso.
  apply psub_0_neg in H4.
  apply not0_implies_positive_deg in H4.
  destruct H4 as [d [H_deg_r H_x] ].
  pose proof (deg_psub a b) as H_deg_r_leq. 
  rewrite H_deg_r in H_deg_r_leq. simpl in H_deg_r_leq.
  assert (H_d_n: (d <= n)%nat).
  { eapply degree_leq_trans. 3: apply H_deg_r_leq. all:auto. }
  specialize (deg_d_has_most_d_roots _ _ H_deg_r H_x).
  intro HX. destruct HX as [X' [H_len_X H_X] ].
  eapply Util.In_pigeon_hole with (X := X ) (X' := X');auto.
  lia.
  intros. apply H_X. unfold root. rewrite eval_psub.
  apply H3 in H4. fqsatz.
Qed.

Lemma degree_leq_tuple: forall n (l:tuple F n),
degree_leq (deg (toPoly l)) (Some (n-1)%nat).
Proof.
Admitted.

Lemma degree_leq_pmul: forall ka kb (a:tuple F ka)(b:tuple F kb),
degree_leq (deg (pmul (toPoly a) (toPoly b))) (Some (ka + kb - 2)%nat).
Proof.
Admitted.

(* Theorem BigMultNoCarry_correct ka kb a b out
  (RANGE1: (ka + kb <= Pos.to_nat q)%nat) (RANGE2: (2 <= ka + kb)%nat):
  BigMultNoCarry ka kb a b out -> BigMultNoCarry_spec ka kb a b out. *)

Theorem BigMultNoCarry_correct ka kb a b out
  (RANGE1: (ka + kb <= Pos.to_nat q)%nat) (RANGE2: (2 <= ka + kb)%nat):
  BigMultNoCarry ka kb a b out -> BigMultNoCarry_spec ka kb a b out.
Proof.
  unfold BigMultNoCarry, BigMultNoCarry_spec, BigMultNoCarry_cons.
  intros. destruct H as [a_poly H]. destruct H as [b_poly H]. destruct H as [out_poly H].
  remember (init_poly ka kb out_poly out True) as init_out.
  pose proof (init_poly_correct out_poly out True) as H_out.
  remember (init_poly ka kb a_poly a init_out) as init_a.
  pose proof (init_poly_correct a_poly a init_out) as H_a.
  remember (init_poly ka kb b_poly b init_a) as init_b.
  pose proof (init_poly_correct b_poly b init_a) as H_b.

  remember (fun (i : nat) (_C : Prop) =>
    _C /\ out_poly [i] = a_poly [i] * b_poly [i] ) as f.

  pose (Inv := fun (i: nat) _C => _C ->
    init_b /\
    forall i0, (i0 < i)%nat -> out_poly [i0] = a_poly [i0] * b_poly [i0] ).

  assert (Hind: forall i, Inv i (D.iter f i init_b)). {
    intros i. unfold Inv; apply D.iter_inv.
    - intuition idtac. lia.
    - intros i0. intros.
      rewrite Heqf in H2.
      intuition idtac.
      destruct (dec (i1 < i0)%nat). auto.
      assert (i1 = i0) by lia. subst. auto.
  }
  (* FIXME: range check *)
  assert (H_ka_kb: (ka + kb - 1 < Pos.to_nat q)%nat) by lia.

  unfold Inv in Hind.
  specialize (Hind (ka + kb -1)%nat).
  subst. intuition idtac.
  assert (H_evals: forall i, (i < ka + kb - 1)%nat -> eval (toPoly out) (F.of_nat q i) = eval (toPoly a) (F.of_nat q i) * eval (toPoly b) (F.of_nat q i)). {
    intros.
    rewrite <- H4, <- H6, <- H8, H2 by lia. reflexivity.
  }
  assert (H_poly: toPoly out = pmul (toPoly a) (toPoly b)). {
    erewrite interpolant_unique with (a:=toPoly out) (b:=pmul (toPoly a) (toPoly b)) (n:=(ka+kb-2)%nat) (X:=List.map (F.of_nat _) (range (ka+kb-1))).
    reflexivity.
    { specialize (degree_leq_tuple (ka+kb-1) out).
      replace ((ka + kb - 1 - 1)%nat) with ((ka + kb - 2)%nat) by lia. auto. }
    { apply degree_leq_pmul. }
    rewrite map_length, range_length.
    (* FIXME: range check *)
    assert ((ka+kb>=2)%nat) by lia.
    lia.
    pose proof Fof_nat_injective.

    eapply Injective_map_NoDup_restrict.
    2: { intros. apply range_range. apply H9. }
    unfold Injective_restrict. intros. apply Fof_nat_injective; (lia || auto).
    (* FIXME: range check *)
    assert (Z.of_nat (ka+kb-1)%nat < q) by lia.
    apply range_nodup.
    intros.
    rewrite eval_ppmul.
    assert (H_xi: exists i, x = F.of_nat _ i /\ (i < ka + kb -1)%nat). {
      apply range_map_preimage in H0. destruct H0. exists x0. intuition idtac. subst. reflexivity.
    }
    destruct H_xi as [i H_xi].
    intuition idtac.
    subst.
    apply H_evals. lia.
  }
  apply H_poly.
Qed.
End BigInt.