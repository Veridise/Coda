open Ast
open Dsl
open Notation

let bit1 = v "bit1"

let bit2 = v "bit2"

let vval = v "val"

let carry = v "carry"

let carry_out = v "carry_out"

let t_val = tfq (toUZ nu ==. zmod (toUZ (bit1 +% bit2 +% carry)) z2)

let t_carry_out = tfq (toUZ nu ==. zdiv (toUZ (bit1 +% bit2 +% carry)) z2)

let fulladder =
  Circuit
    { name= "fulladder"
    ; inputs= [("bit1", tf_binary); ("bit2", tf_binary); ("carry", tf_binary)]
    ; outputs= [("val", t_val); ("carry_out", t_carry_out)]
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
