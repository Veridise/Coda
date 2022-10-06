Require Import Crypto.Spec.ModularArithmetic.
Require Import Circom.Circom.

Class Default (T: Type) := { default: T }.

#[global] Instance F_default: Default F := { default := 0 }.