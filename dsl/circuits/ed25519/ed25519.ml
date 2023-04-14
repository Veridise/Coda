open Ast
open Dsl
open Notation

let bit = v "bit"

let bit1 = v "bit1"

let bit2 = v "bit2"

let vval = v "val"

let carry = v "carry"

let carry_out = v "carry_out"

(* fulladder *)

let t_val_fa = tfq (toUZ nu ==. zmod (toUZ (bit1 +% bit2 +% carry)) z2)

let t_carry_out_fa = tfq (toUZ nu ==. zdiv (toUZ (bit1 +% bit2 +% carry)) z2)

let fulladder =
  Circuit
    { name= "fulladder"
    ; inputs= [("bit1", tf_binary); ("bit2", tf_binary); ("carry", tf_binary)]
    ; outputs= [("val", t_val_fa); ("carry_out", t_carry_out_fa)]
    ; dep= Some ((f2 *% carry_out) +% vval ==. bit1 +% bit2 +% carry)
    ; body=
        elet "val" star
          (elet "u0"
             (assert_eq (vval *% (vval -% f1)) f0)
             (elet "u1"
                (assert_eq (toUZ vval) (zmod (toUZ (bit1 +% bit2 +% carry)) z2))
                (elet "carry_out" star
                   (elet "u2"
                      (assert_eq (carry_out *% (carry_out -% f1)) f0)
                      (elet "u3"
                         (assert_eq (toUZ carry_out)
                            (zdiv (toUZ (bit1 +% bit2 +% carry)) z2) )
                         (pair vval carry_out) ) ) ) ) ) }

(* onlycarry *)

let t_val_oc = tfq (toUZ nu ==. zmod (toUZ (bit +% carry)) z2)

let t_carry_out_oc = tfq (toUZ nu ==. zdiv (toUZ (bit +% carry)) z2)

let onlycarry =
  Circuit
    { name= "onlycarry"
    ; inputs= [("bit", tf_binary); ("carry", tf_binary)]
    ; outputs= [("val", t_val_oc); ("carry_out", t_carry_out_oc)]
    ; dep= Some ((f2 *% carry_out) +% vval ==. bit +% carry)
    ; body=
        elet "val" star
          (elet "u0"
             (assert_eq (vval *% (vval -% f1)) f0)
             (elet "u1"
                (assert_eq (toUZ vval) (zmod (toUZ (bit +% carry)) z2))
                (elet "carry_out" star
                   (elet "u2"
                      (assert_eq (carry_out *% (carry_out -% f1)) f0)
                      (elet "u3"
                         (assert_eq (toUZ carry_out)
                            (zdiv (toUZ (bit +% carry)) z2) )
                         (pair vval carry_out) ) ) ) ) ) }
