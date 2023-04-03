open Ast
open Dsl

let n = v "n"

let m = v "m"

let k = v "k"

let vin = v "in"

let s = v "small"

let med = v "medium"

let b = v "big"

(* { v : F | toUZ(v) <= 2**n - 1 } *)
let tf_2n n = tfe (leq (toUZ nu) (zsub (zpow z2 n) z1))

let split =
  Circuit
    { name= "Split"
    ; inputs= [("n", tnat); ("m", tnat); ("in", tf)]
    ; outputs= [("small", tf_2n n); ("big", tf_2n m)]
    ; dep= None
    ; body=
        (* small <-- in mod 2 ^ n *)
        elet "small" star
          (* big <-- in div 2 ^ n *)
          (elet "big" star
             (* Constrain outputs to have the right number of bits *)
             (elet "u0"
                (assert_eq vin (fadd s (fmul b (fpow f2 n))))
                (* in === small + big * 2 ^ n *)
                (make [call "Num2Bits" [n; s]; call "Num2Bits" [m; b]]) ) ) }

let split_three =
  Circuit
    { name= "SplitThree"
    ; inputs= [("n", tnat); ("m", tnat); ("k", tnat); ("in", tf)]
    ; outputs= [("small", tf_2n n); ("medium", tf_2n m); ("big", tf_2n k)]
    ; dep= None
    ; body=
        (* small <-- in mod 2 ^ n *)
        elet "small" star
          (* medium <-- (in div 2 ^ n) mod 2 ^ m *)
          (elet "medium" star
             (* big <-- in div 2 ^ (n + m) *)
             (elet "big" star
                (* Constrain outputs to have the right number of bits *)
                (elet "u0"
                   (* in === small + medium * 2 ^ n + big * 2 ^ (n + m) *)
                   (assert_eq vin
                      (fadd s
                         (fadd
                            (fmul med (fpow f2 n))
                            (fmul b (fpow f2 (fadd n m))) ) ) )
                   (make
                      [ call "Num2Bits" [n; s]
                      ; call "Num2Bits" [m; med]
                      ; call "Num2Bits" [k; b] ] ) ) ) ) }
