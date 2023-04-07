Require Import Crypto.Spec.ModularArithmetic.
Require Import Circom.Circom.

Class Default (T: Type) := { default: T }.

#[global] Instance F_default: Default F := { default := 0 }.
#[global] Instance F_F_default: Default (F*F) := { default := (0%F,0%F) }.