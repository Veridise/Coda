open Ast
open Dsl
open Notation

let z254 = zn 254

let i = v "i"

let n = v "n"

let x = v "x"

let z = v "z"

let vin = v "in"

let out = v "out"

let n2b = v "n2b"

(* is_negative (in : F) : { F | binary nu /\ nu = 1 -> (toSZ in < 0) /\ nu = 0 -> ~(toSZ in < 0) } *)
let is_negative =
  Circuit
    { name= "IsNegative"
    ; inputs= [("in", tf)]
    ; outputs= [("out", tfq (ind_dec nu (toSZ vin <. z0)))]
    ; dep= None
    ; body= elet "n2b" (call2 "Num2Bits" z254 vin) (call1 "Sign" n2b) }

(* is_positive (in : F) : { F | binary nu /\ nu = 1 -> (0 < toSZ in) /\ nu = 0 -> ~(0 < toSZ in) } *)
let is_positive =
  Circuit
    { name= "IsPositive"
    ; inputs= [("in", tf)]
    ; outputs= [("out", tfq (ind_dec nu (z0 <. toSZ vin)))]
    ; dep= None
    ; body=
        elet "n2b"
          (call2 "Num2Bits" z254 vin)
          (elets
             [("s", call1 "Sign" n2b); ("isz", call1 "IsZero" vin)]
             ((f1 -% v "s") *% (f1 -% v "isz")) ) }

(* relu (in : F) : { F | toSZ nu = max 0 (toSZ in) } *)
let relu =
  Circuit
    { name= "ReLU"
    ; inputs= [("in", tf)]
    ; outputs= [("out", tfe (toSZ nu =. zmax z0 (toSZ vin)))]
    ; dep= None
    ; body= elet "isp" (call1 "IsPositive" vin) (vin *% v "isp") }

(* poly (n : F) (in : F) : { F | nu = in * (in + n) } *)
let poly =
  Circuit
    { name= "Poly"
    ; inputs= [("n", tf); ("in", tf)]
    ; outputs= [("out", tfe (nu =. vin *% (vin +% n)))]
    ; dep= None
    ; body= (vin *% vin) +% (n *% vin) }
