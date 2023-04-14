open Ast
open Dsl
open Notation

let n = v "n"

let m = v "m"

let k = v "k"

let vin = v "in"

let small = v "small"

let med = v "medium"

let big = v "big"

(* { v : F | toUZ(v) <= 2**n - 1 } *)
let tf_2n n = tfe (leq (toUZ nu) (zsub (zpow z2 n) z1))

let split =
  Circuit
    { name= "Split"
    ; inputs= [("n", (attach (lift (nu <. CPLen)) tnat)); ("m", (attach (lift (nu <. CPLen)) tnat)); ("in", tf)]
    ; outputs= [("small", tf_2n n); ("big", tf_2n m)]
    ; dep= Some (vin ==. small +% (big *% (f2 ^%n)))
    ; body=
        elets
          [ ("small", star)
          ; ("big", star)
          ; ("bits_small", call "Num2Bits" [n; small])
          ; ("bits_big", call "Num2Bits" [m; big])
          ; (* in === small + big * 2 ^ n *)
            ("u0", vin === small +% (big *% (f2 ^% n))) ]
          (pair small big) }

let split_three =
  Circuit
    { name= "SplitThree"
    ; inputs= [("n", (attach (lift (nu <. CPLen)) tnat)); ("m", (attach (lift (nu <. CPLen)) tnat)); ("k", (attach (lift (nu <. CPLen)) tnat)); ("in", tf)]
    ; outputs= [("small", tf_2n n); ("medium", tf_2n m); ("big", tf_2n k)]
    ; dep= Some (vin ==. small +% (med *% (f2 ^% n)) +% (big *% (f2 ^% (n +. m))))
    ; body=
    elets
    [ ("small", star)
    ; ("medium", star)
    ; ("big", star)
    ; ("bs", call "Num2Bits" [n; small])
    ; ("bm", call "Num2Bits" [m; med])
    ; ("bb", call "Num2Bits" [k; big])
     (* in === small + medium * 2 ^ n + big * 2 ^ (n + m) *)
    ; ("u0", vin === small +% (med *% (f2 ^% n)) +% (big *% (f2 ^% (n +. m)))) ]
    (make [small; med; big]) }