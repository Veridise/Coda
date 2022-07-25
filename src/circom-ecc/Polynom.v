Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Setoid.
Require Import Coq.Lists.List.
Require Import Lia.
Open Scope signature_scope.

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
Require Import Coq.Lists.ListSet.
Require Import Crypto.Util.Decidable Crypto.Util.Notations.
Require Import Crypto.Algebra.Ring.

Require Import Util.

Section Polynomial.

Context {F eq zero one opp add sub mul inv div}
        {fld:@Hierarchy.field F eq zero one opp add sub mul inv div}
        {eq_dec:DecidableRel eq}
        {pow: F -> nat -> F}.

Local Infix "==" := eq. 
(* Local Notation "a <> b" := (not (a = b)). *)
(* Local Notation "a <> b" := (not (a = b)) : type_scope. *)
Local Infix "==" := eq : type_scope. 
Local Notation "0" := zero.  Local Notation "1" := one.
Local Infix "+" := add. Local Infix "*" := mul.
Local Infix "-" := sub. Local Infix "/" := div.
Local Infix "^" := pow.

Ltac invert H := inversion H; subst; clear H.


(* Formalization due to 
 * https://coq-club.inria.narkive.com/cL8AtXMS/how-could-i-do-polynomials-in-coq *)

Definition polynomial := list F.

Inductive empty_poly : polynomial -> Prop :=
| empty_poly_nil : empty_poly nil
| empty_poly_cons : forall f x, x == 0 -> empty_poly f -> empty_poly (x::f).

Definition p0 : polynomial := nil.

(* A [polynomial] with trailing zeros is equivalent to one without. *)
Reserved Notation "a ~ b" (at level 20).
Inductive eq_poly : polynomial -> polynomial -> Prop :=
| eq_poly_empty : forall f g, empty_poly f -> empty_poly g -> eq_poly f g
| eq_poly_cons : forall x y f g, eq_poly f g -> x == y -> eq_poly (x::f) (y::g).
Notation "a ~ b" := (eq_poly a b) (at level 20).

Hint Constructors empty_poly : core.
Hint Constructors eq_poly : core.

Hint Extern 10 (_ == _) => fsatz : core.
Hint Extern 10 (?A ~ ?A) => reflexivity : core.

Lemma eq_poly_empty_imp: forall f g, f ~ g -> empty_poly g -> empty_poly f.
Proof.
  intros f g H.
  induction H; intro; auto.
  invert H1. auto.
Qed.


Instance eq_poly_equivalence : Equivalence eq_poly.
Proof.
  constructor.
  (* reflexive *)
  - intro. induction x; auto. 
  (* symmetric *)
  - intros x y H. 
    induction H.
    + apply eq_poly_empty;auto.
    + apply eq_poly_cons;auto.
  (* transitive *)
    - intros x y z H1 H2. revert H2. revert z.
      induction H1; intros z H2.
    + apply eq_poly_empty; auto.
      induction H2; auto. invert H0.
      constructor; auto.
    + invert H2; auto.
      apply eq_poly_empty; auto. invert H0.
      constructor. fsatz. eapply eq_poly_empty_imp; eauto.
Qed.

(* Lemma p0_empty: empty_poly p0.
Proof. constructor. Qed. *)

Lemma empty_eq_0: forall f, empty_poly f -> f ~ p0.
Proof. auto. Qed.

Instance cons_Proper: forall c, Proper (eq_poly ==> eq_poly) (cons c).
Proof.
  intros. unfold Proper, respectful.
  intros f g H.
  induction H; auto.
Qed.

(**************************************
 *            Evaluation              *
 **************************************)
Fixpoint peval x f : F :=
  match f with
  | nil => 0
  | c::f' => c + x * peval x f'
  end.

Notation "f ([ x ]) " := (peval x f) (at level 19).

Lemma peval_empty_zero (f: polynomial): 
  empty_poly f -> forall (x: F),  f([x]) == 0.
Proof.
  intros. induction H; simpl; auto.
Qed.

(* proof that peval depends only upon the equivalence class of the
* polynomial, not its concrete representation as a list *)
(* Instance peval_Proper: forall x, Proper (eq_poly ==> eq) (peval x).
Proof.
  intros; unfold Proper; unfold respectful; intros.
  induction H.
  rewrite peval_empty_zero; auto.
  rewrite peval_empty_zero; auto. fsatz.
  simpl; rewrite IHeq_poly; fsatz.
Defined. *)

Instance peval_Proper: Proper (eq ==> eq_poly ==> eq) peval.
Proof.
  intros; unfold Proper; unfold respectful; intros.
  induction H0.
  - repeat rewrite peval_empty_zero; auto.
  - simpl. rewrite IHeq_poly. fsatz.
Defined.

(* 
(* accumulative evaluation *)
Fixpoint aeval' (i: nat) (x: F) (cs: polynomial) : F :=
  match cs with
  | nil => 0
  | c::cs' => c * x^i + eval' (S i) x cs'
  end.

Definition aeval := eval' 0.

Lemma peval *)


(**************************************
 *     Evaluation under context       *
 **************************************)

Definition peval_then (op: F -> F -> F) (x: F) (f g: polynomial) : F :=
  op (f ([x])) (g ([x])).

Definition peval_then_add := peval_then add.
Definition peval_then_sub := peval_then sub.
Definition peval_then_mul := peval_then mul.
Definition peval_then_div := peval_then div.

Instance peval_then_add_Proper:
  Proper (eq ==> eq_poly ==> eq_poly ==> eq) peval_then_add.
Proof.
  intros. unfold Proper. unfold respectful. intros.
  unfold peval_then_add, peval_then.
  rewrite H0. rewrite H1.
  rewrite H.
  reflexivity.
Qed.

Instance peval_then_sub_Proper:
  Proper (eq ==> eq_poly ==> eq_poly ==> eq) peval_then_sub.
Proof.
  intros. unfold Proper. unfold respectful. intros.
  unfold peval_then_sub, peval_then.
  rewrite H0. rewrite H1.
  rewrite H.
  reflexivity.
Qed.

Instance peval_then_mul_Proper:
  Proper (eq ==> eq_poly ==> eq_poly ==> eq) peval_then_mul.
Proof.
  intros. unfold Proper. unfold respectful. intros.
  unfold peval_then_mul, peval_then.
  rewrite H0. rewrite H1.
  rewrite H.
  reflexivity.
Qed.

Instance peval_then_div_Proper:
  Proper (eq ==> eq_poly ==> eq_poly ==> eq) peval_then_div.
Proof.
  intros. unfold Proper. unfold respectful. intros.
  unfold peval_then_div, peval_then.
  rewrite H0. rewrite H1.
  rewrite H.
  reflexivity.
Qed.


(**************************************
 *            Coefficient             *
 **************************************)

Definition coeff (i: nat) (f: polynomial) : F := nth i f 0.

Notation "f [ i ]" := (coeff i f).

Lemma nth_nil: forall {A: Type} i (d: A), nth i nil d = d.
Proof.
  intros. destruct i; reflexivity.
Qed.

Lemma coeff_empty: forall f, empty_poly f -> forall i, f[i] == 0.
Proof.
  intros f H. unfold coeff. induction H; intros.
  - rewrite nth_nil. fsatz.
  - destruct i.
    + fsatz.
    + cbn. apply IHempty_poly.
Qed.

Lemma coeff_equal: forall f g, f ~ g -> forall i, f[i] == g[i].
Proof.
  intros f g H. induction H; simpl; intros.
  - repeat rewrite coeff_empty by auto. reflexivity.
  - destruct i.
    + fsatz.
    + apply IHeq_poly.
Qed.


(**************************************
 *               Degree               *
 **************************************)

Definition degree := option nat.
Definition mk_degree (n: nat) := Some n.
Fixpoint deg (f: polynomial) : degree := 
  match f with
  | nil => None
  | c::f' =>
    match deg f' with
    | Some d => Some (S d)
    | None => if eq_dec c 0 then None else Some O
    end
  end.

Definition degree_leqb d1 d2 :=
  match d1, d2 with
  | Some d1, Some d2 => (d1 <=? d2)%nat
  | None, _ => true
  | _, None => false
  end.
Definition degree_leq d1 d2 : Prop := degree_leqb d1 d2 = true.

Definition degree_max d1 d2 :=
  match d1, d2 with
  | None, _ => d2
  | _, None => d1
  | Some d1, Some d2 => Some (max d1 d2)
  end.

Definition degree_min d1 d2 :=
  match d1, d2 with
  | None, _ => d1
  | _, None => d2
  | Some d1, Some d2 => Some (min d1 d2)
  end.

Definition degree_add d1 d2 :=
  match d1, d2 with
  | None, _ => d2
  | _, None => d1
  | Some d1, Some d2 => Some (d1 + d2)%nat
  end.


(**************************************
 *             Arithmetic             *
 **************************************)

Definition uncurry {A B C: Type} (f: A -> B -> C) := fun xy => f (fst xy) (snd xy).
Fixpoint pairwise {A: Type} (op: A -> A -> A) (f g: list A) : list A :=
  match f, g with
  | nil, _ => g
  | _, nil => f
  | (a :: f), (b :: g) => (op a b) :: pairwise op f g
  end.

Definition padd : polynomial -> polynomial -> polynomial := pairwise add.
Notation "f p+ g" := (padd f g) (at level 18).

Definition pscale (k: F) : polynomial -> polynomial := map (fun a => k * a).
Notation "k p$ f" := (pscale k f) (at level 17).

Definition psub (f g: polynomial) : polynomial := padd f (pscale (opp 1) g).
Notation "f p- g" := (psub f g) (at level 18).

Fixpoint pmul (f g: polynomial) : polynomial :=
  match f with
  | nil => nil
  | (a :: f') => padd (pscale a g) (0 :: (pmul f' g))
  end.

Notation "f p* g" := (pmul f g) (at level 17).



(**************************************
 *     Arithmetic and Evaluation      *
 **************************************)

Lemma peval_padd: forall f g x,
  (f p+ g) ([x]) == f ([x]) + g ([x]).
Proof.
  induction f; simpl; intros.
  - fsatz.
  - destruct g; simpl.
    + fsatz.
    + rewrite IHf. fsatz.
Qed.

Lemma peval_pscale: forall f k x,
  (k p$ f) ([x]) == k * f ([x]).
Proof.
  induction f; simpl; intros.
  - fsatz.
  - rewrite IHf. fsatz.
Qed.

Lemma eval_popp: forall f x,
  ((opp 1) p$ f) ([x]) == opp (f ([x])).
Proof.
  induction f; simpl; intros.
  - fsatz.
  - rewrite IHf. fsatz.
Qed.


Lemma eval_psub: forall f g x,
  (f p- g) ([x]) == f ([x]) - g ([x]).
Proof.
  unfold psub. intros. rewrite peval_padd. rewrite eval_popp. fsatz.
Qed.

Lemma padd_0_r: forall f g, g ~ p0 -> f p+ g ~ f.
Proof.
  induction f; unfold padd in *; intros; auto.
  invert H. invert H0.
  - simpl. auto.
  - simpl. apply eq_poly_cons; auto.
Qed.
  
Lemma padd_comm: forall f g,
  padd f g ~ padd g f.
Proof.
  induction f; unfold padd in *; simpl; intros.
  - rewrite padd_0_r; auto.
  - destruct g as [|b g]; simpl. auto.
    rewrite IHf. auto. 
Qed.

(* Instance padd_r_p0_Proper:
  Proper (eq_poly ==> eq_poly) (padd p0).
Proof.
  intros f g H. induction H.
  - auto.
  - apply eq_poly_cons; auto.
Qed. *)

Instance padd_r_Proper: forall f,
  Proper (eq_poly ==> eq_poly) (padd f).
Proof.
  unfold Proper, respectful.
  intros f g1 g2 H. generalize dependent f.
  induction H as [g1 g2 H1 H2 | c d g1 g2 Hcd IH]; unfold padd in *; intros.
  - apply empty_eq_0 in H1, H2. repeat rewrite padd_eq0_r; auto.
    repeat rewrite padd_0_r; auto.
  - destruct f as [|a f]; simpl; auto.
Qed.

Instance padd_Proper:
  Proper (eq_poly ==> eq_poly ==> eq_poly) padd.
Proof.
  unfold Proper, respectful.
  intros f1 g1 H.
  induction H as [f1 g1 Hf Hg| c d f1 g1]; simpl; intros f2 g2 H2.
  - apply empty_eq_0 in Hf, Hg.
    rewrite padd_comm. rewrite Hf.
    rewrite padd_comm with (f := g1). rewrite Hg.
    repeat rewrite padd_0_r; auto.
  - unfold padd in *. invert H2.
    + apply empty_eq_0 in H1, H3.
      rewrite H1, H3. repeat rewrite padd_0_r; auto.
    + simpl. rewrite IHeq_poly with (x:=f) (y:=g); auto.
Qed.

Lemma pscale_p0: forall f k, f ~ p0 -> k p$ f ~ p0.
Proof.
  induction f; simpl; intros; auto.
  invert H. invert H0.
  apply eq_poly_empty; auto.
  constructor; auto.
  eapply eq_poly_empty_imp; auto.
Qed.

Instance pscale_Proper:
  Proper (eq ==> eq_poly ==> eq_poly) pscale.
Proof.
  intros x y Hxy f g Hfg.
  induction Hfg.
  + repeat rewrite pscale_p0; auto.
  + simpl. apply eq_poly_cons; auto.
Qed.

Instance psub_Proper:
  Proper (eq_poly ==> eq_poly ==> eq_poly) psub.
Proof.
  intros f1 g1 H1 f2 g2 H2.
  unfold psub. rewrite H1, H2. auto.
Qed.

Instance pmul_Proper:
  Proper (eq_poly ==> eq_poly ==> eq_poly) pmul.
Abort.

Lemma pmul_0_r: forall f, f p* p0 ~ p0.
Proof.
  induction f; auto.
  simpl. unfold padd. rewrite IHf. simpl. auto.
Qed.

Lemma eval_repeat_0: forall k x, (List.repeat 0 k)([x]) == 0.
Proof.
  induction k; intros; simpl; auto.
  rewrite IHk. auto.
Qed.

Lemma peval_ppmul: forall f g x, (f p* g)([x]) == f([x]) * g([x]).
Proof.
  induction f; simpl; intros; auto.
  rewrite peval_padd.
  rewrite peval_pscale.
  simpl. rewrite IHf. fsatz.
Qed.


(* 

(* Hanzhi *)

Definition toPoly {m} (xs: tuple (F q) m) : polynomial := to_list m xs.

Lemma toPoly_length: forall {m} (xs: tuple (F q) m),
  length (toPoly xs) = m.
Proof.
  intros. apply length_to_list.
Qed.

Definition coeff (i: nat) (cs: polynomial) := nth i cs 0.

Lemma coeff_nth: forall {m} (xs: tuple (F q) m) i,
  coeff i (toPoly xs) = nth_default 0 i xs.
Proof.
  unfold coeff. unfold toPoly. intros.
  rewrite <- nth_default_eq. apply nth_default_to_list.
Qed.


Lemma firstn_toPoly: forall m (x: tuple (F q) m),
  firstn m (toPoly x) = toPoly x.
Proof.
  intros.
  apply firstn_all2. unfold toPoly.
  rewrite length_to_list;lia.
Qed.

Lemma eval_app': forall cs0 cs1 n x,
  eval' n (cs0 ++ cs1) x = eval' n cs0 x + eval' (n + N.of_nat (length cs0)) cs1 x.
Proof.
  induction cs0;simpl;intros.
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



(**************************************
 *       Arithmetic and Degree        *
 **************************************)

Lemma deg_padd: forall p q,
  degree_leq (deg (p p+ q)) (degree_max (deg p) (deg q)).
Abort.

Lemma deg_pmul: forall p q,
  degree_leq (deg (p p* q)) (degree_add (deg p) (deg q)).
Abort.

Lemma deg_pscale: forall p k,
  degree_leq (deg (pscale k p)) (deg p).
Abort.

Lemma deg_psub: forall p q, (*11*)
  degree_leq (deg (p p- q)) (degree_max (deg p) (deg q)).
Admitted.

Lemma degree_leq_tuple: forall n (l:tuple (F q) n),
degree_leq (deg (toPoly l)) (Some (n-1)%nat).
Proof.
Admitted.

Lemma degree_leq_pmul: forall ka kb (a:tuple (F q) ka)(b:tuple (F q) kb),
degree_leq (deg (pmul (toPoly a) (toPoly b))) (Some (ka + kb - 2)%nat).
Proof.
Admitted.


(**************************************
 *        Unique Interpolant          *
 **************************************)

Definition root x p := peval x p == 0.

Definition linear a := (opp a :: 1 :: nil).

Lemma psub_0: forall p q,
  (p p- q) ~ p0 <-> p ~ q.
Abort.

Lemma eq_poly_decidable: forall p q, (*11*)
  p ~ q \/ ~ (p ~ q).
Admitted.

Lemma psub_0_neg: forall p q, (*11*)
  ~((p p- q) ~ p0) <-> ~(p ~ q).
Admitted.

Lemma not0_implies_positive_deg: forall p, (*11*)
  ~ (p ~ p0) -> exists n, deg p = Some n /\ (n > 0)%nat.
Admitted.

Lemma deg_d_has_most_d_roots: forall p d, (*11*)
  deg p = Some d ->
  (d > 0)%nat ->
  exists X, length X = d /\ forall x, root x p -> In x X.
Admitted.


Lemma pdiv: forall a b,
  ~ (a ~ p0) ->
  exists q r, a ~ ((q p* b) p+ r) /\
  (r ~ p0 \/ degree_leq (deg r) (deg b)).
Abort.

Lemma factor_root: forall p a, root a p ->
  exists q, p ~ (linear a p* q).
Abort.

Lemma In_pigeon_hole: forall {A: Type} (X X': list A), (*11*)
  (length X > length X')%nat ->
  (forall x, In x X -> In x X') ->
  False.
Proof.
Admitted.

Lemma unique_interpolant: forall p q n X,
  deg p = Some n ->
  deg q = Some n ->
  NoDup X ->
  length X = S n ->
  (forall x, In x X -> peval x p == peval x q) ->
  p ~ q.
Proof.
  (* Proof: https://inst.eecs.berkeley.edu/~cs70/fa14/notes/n7.pdf *)
  intros.
  destruct (eq_poly_decidable p q).
  trivial.
  exfalso.
  apply psub_0_neg in H4.
  apply not0_implies_positive_deg in H4.
  destruct H4 as [d [H_deg_r H_x] ].
  pose proof (deg_psub p q) as H_deg_r_leq. rewrite H, H0 in H_deg_r_leq.
  rewrite H_deg_r in H_deg_r_leq. simpl in H_deg_r_leq.
  assert (H_d_n: (d <= n)%nat). apply leb_complete in H_deg_r_leq. lia.
  replace (degree_max (Some n) (Some n)) with (Some n) in H_deg_r_leq by (simpl; f_equal; lia).
  specialize (deg_d_has_most_d_roots _ _ H_deg_r H_x).
  intro HX. destruct HX as [X' [H_len_X H_X] ].
  eapply In_pigeon_hole with (X := X ) (X' := X').
  lia.
  intros. apply H_X. unfold root. rewrite peval_psub.
  apply H3 in H4. fsatz.
Qed.


(* Hanzhi *)

Lemma deg_psub: forall p q, (*11*)
  degree_leq (deg (psub p q)) (degree_max (deg p) (deg q)).
Proof.
Admitted.

Lemma eq_poly_decidable: forall p q : polynomial, (*11*)
  p = q \/ ~ (p = q).
Proof.
  intros. pose proof (dec_eq_list p q0). destruct H;auto.
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

Theorem interpolant_unique: forall (a b: polynomial) n (X: list (F q)),
  degree_leq (deg a) (Some n) ->
  degree_leq (deg b) (Some n) ->
  (length X > n)%nat ->
  NoDup X ->
  (forall x, In x X -> eval a x = eval b x) ->
  a = b.
Proof.
  (* Proof: https://inst.eecs.berkeley.edu/~cs70/fa14/notes/n7.pdf *)
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
  eapply In_pigeon_hole with (X := X ) (X' := X');auto.
  lia.
  intros. apply H_X. unfold root. rewrite eval_psub.
  apply H3 in H4. fqsatz.
Qed.
 *)

End Polynomial.