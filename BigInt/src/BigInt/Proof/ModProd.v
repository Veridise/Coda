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

Require Import Crypto.Util.Decidable. (* Crypto.Util.Notations. *)
Require Import Coq.setoid_ring.Ring_theory Coq.setoid_ring.Field_theory Coq.setoid_ring.Field_tac.
Require Import Ring.

From Circom Require Import Circom Default Util DSL Tuple ListUtil LibTactics Simplify.
From Circom Require Import Repr ReprZ.
From Circom.CircomLib Require Import Bitify Comparators.
From Circom.BigInt.Definition Require Import ModProd.
(* Circuit:
* https://github.com/yi-sun/circom-pairing/blob/master/circuits/bigint.circom
*)

Module ModProd.

Module D := DSL.
Module Cmp := Comparators.
Module RZU := ReprZUnsigned.
Module RZ := RZU.RZ.
Module R := Repr.

Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope F_scope.
Local Open Scope circom_scope.
Local Open Scope tuple_scope.

Local Coercion Z.of_nat: nat >-> Z.
Local Coercion N.of_nat: nat >-> N.

Module N := Bitify.Num2Bits.
Module B := Bitify.Bits2Num.

Section _ModProd.
Context {n: nat}.

Definition cons (a b prod carry: F) := 
  exists n2b: (@N.t (2*n)),
  n2b.(N._in) = a*b /\
  exists (b2n1: @B.t n) (b2n2: @B.t n),
  D.iter (fun (i: nat) (cons : Prop) => cons /\
    b2n1.(B._in)[i] = n2b.(N.out)[i] /\
    b2n2.(B._in)[i] = n2b.(N.out)[i + n])
  n True /\
  prod = b2n1.(B.out) /\
  carry = b2n2.(B.out).

Record t := { a: F; b: F; prod: F; carry: F; _cons: cons a b prod carry}.

Local Notation "[| xs |]" := (Bitify.R.as_le 1 xs).

#[local]Hint Extern 10 (Forall _ (firstn _ _)) => apply Forall_firstn : core.
#[local]Hint Extern 10 (Forall _ (skipn _ _)) => apply Forall_skipn : core.

Theorem soundness: forall (c: t),
  2 * n <= k ->
  let '(a,b,prod,carry) := (c.(a), c.(b), c.(prod), c.(carry)) in
  carry * 2^n + prod = a * b /\
  prod | (n).
Proof with (lia || rewrite_length || fqsatz || eauto).
  unwrap_C.
  intros c Hn. destruct c as [a b prod carry _cons].
  destruct _cons as [n2b [n2b_in [b2n1 [b2n2 [loop [Pprod Pcarry]]]]]].
  simpl.
  rem_iter.
  pose proof (N.soundness n2b) as SN.
  pose proof (B.soundness b2n1) as SB1.
  pose proof (B.soundness b2n2) as SB2.
  pose proof SN as Hrepr.
  destruct Hrepr as [_ [Sout Has]]. 
  pose_lengths.

  rewrite n2b_in in *. clear n2b_in.

  pose (Inv := fun (i: nat) (_cons: Prop) => _cons ->
    (* forall (j: nat), j < i ->
    'b2n1.(B._in)[:j] = 'n2b.(N.out)[:j] /\
    'b2n2.(B._in)[:j] = 'n2b.(N.out)[:j+n] *)
    'b2n1.(B._in)[:i] = 'n2b.(N.out)[:i] /\
    'b2n2.(B._in)[:i] = 'n2b.(N.out)[n:][:i]
  ).

  assert (Hinv: Inv n%nat (D.iter f n%nat True)). {
    apply DSL.iter_inv; unfold Inv.
    - easy.
    - intros i _cons IH Hi Hstep.
      subst f; lift_to_list; intuit.
      eapply firstn_congruence; fold_default; (lia || eauto).
      eapply firstn_congruence; auto.
      rewrite skipn_nth. fold_default. lrewrite. f_equal. lia.
  }
  pose_lengths.
  specialize (Hinv loop). clear Inv.
  firstn_all. 
  (* why didn't firstn *)
  rewrite firstn_all2 with (l:=' B._in b2n2) in Hinv by lia.
  destruct Hinv as [H H'].
  rewrite H, H', SB1, SB2, Pprod, Pcarry in *; auto.
  unfold R.as_le2 in *.
  split.
  rewrite Has.
  rewrite firstn_all2 with (l:=(' N.out n2b [n:]))...
  remember ('N.out n2b [:n]) as fst. remember ('N.out n2b [n:]) as snd.
  erewrite <- firstn_skipn with (l:='N.out n2b) (n:=n).
  rewrite R.as_le_app... subst. fqsatz.
  applys_eq R.repr_le_ub'; auto...
  Unshelve. all:exact F.zero.
Qed.

End _ModProd.
End ModProd.