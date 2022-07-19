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

Module Type POLYNOMIAL.
  Local Open Scope F_scope.
  Parameter q: positive.
  Axiom q_prime: prime q.
  Parameter polynomial : Set.
  Parameter zero : polynomial.
  Parameter add: polynomial -> polynomial -> polynomial.
  Parameter scale: polynomial -> F q -> polynomial.
  Parameter mul: polynomial -> polynomial -> polynomial.
  Parameter from_list: list (F q) -> polynomial.
  Parameter to_list: polynomial -> list (F q).
  Parameter degree: polynomial -> option nat.
  Parameter coeff: polynomial -> nat -> F q -> F q.
  Parameter eval: polynomial -> (F q) -> (F q).
  Axiom eval_add: forall a b x,
    eval (add a b) x = eval a x + eval b x.
  Axiom eval_scale: forall a k x,
    eval (scale a k) x = k * eval a x.
  Axiom eval_mul: forall a b x,
    eval (mul a b) x = eval a x * eval b x.
  
  (* If polynomials a and b of degree n agree on >n inputs, then they are identical. *)
  Axiom same_poly: forall (a b: polynomial) n (X: set (F q)),
    degree a = Some n ->
    degree b = Some n ->
    (length X > n)%nat ->
    (forall x, In x X -> eval a x = eval b x) ->
    a = b.

  Axiom from_list_coeff: forall l i d,
    coeff (from_list l) i d = nth i l d.
  
  (* mult behavior in turns of sums *)

  (* To be continued *)
  Close Scope F_scope.
  
End POLYNOMIAL.

(* Possible implementations: *)
(* https://coq-club.inria.narkive.com/cL8AtXMS/how-could-i-do-polynomials-in-coq *)
(* or other coq math lib *)