open Ast
open Dsl
open Typecheck
open Bitify

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
        [ (* small <-- in mod 2 ^ n *)
          slet "small" star
        ; (* big <-- in div 2 ^ n *)
          slet "big" star
        ; (* Constrain outputs to have the right number of bits *)
          assert_eq (v "_n2b_s") (call "Num2Bits" [n; s])
        ; assert_eq (v "_n2b_b") (call "Num2Bits" [m; b])
        ; (* in === small + big * 2 ^ n *)
          assert_eq vin (fadd s (fmul b (fpow f2 n))) ] }

let split_three =
  Circuit
    { name= "SplitThree"
    ; inputs= [("n", tnat); ("m", tnat); ("k", tnat); ("in", tf)]
    ; outputs= [("small", tf_2n n); ("medium", tf_2n m); ("big", tf_2n k)]
    ; dep= None
    ; body=
        [ (* small <-- in mod 2 ^ n *)
          slet "small" star
        ; (* medium <-- (in div 2 ^ n) mod 2 ^ m *)
          slet "medium" star
        ; (* big <-- in div 2 ^ (n + m) *)
          slet "big" star
        ; (* Constrain outputs to have the right number of bits *)
          assert_eq (v "_n2b_s") (call "Num2Bits" [n; s])
        ; assert_eq (v "_n2b_m") (call "Num2Bits" [m; med])
        ; assert_eq (v "_n2b_b") (call "Num2Bits" [k; b])
        ; (* in === small + medium * 2 ^ n + big * 2 ^ (n + m) *)
          assert_eq vin
            (fadd s (fadd (fmul med (fpow f2 n)) (fmul b (fpow f2 (fadd n m)))))
        ] }

let deltas = add_to_delta d_empty num2bits

let check_split = typecheck_circuit deltas split

let check_split_three = typecheck_circuit deltas split_three
