open Ast
open Dsl
open Notation

let i = v "i"

let n = v "n"

let x = v "x"

let z = v "z"

let vin = v "in"

let out = v "out"

(* FIXME: should be sign(num2bits(vin)) *)

let sign =
  Circuit
    { name= "Sign"
    ; inputs= [("in", tf)]
    ; outputs= [("out", tfq (ind_dec nu (toSZ vin <. z0)))]
    ; dep= None
    ; body= unit_val }

let is_negative =
  Circuit
    { name= "IsNegative"
    ; inputs= [("in", tf)]
    ; outputs= [("out", tfq (ind_dec nu (toSZ vin <. z0)))]
    ; dep= None
    ; body= call1 "Sign" vin }

let is_positive =
  Circuit
    { name= "IsPositive"
    ; inputs= [("in", tf)]
    ; outputs= [("out", tfq (ind_dec nu (z0 <. toSZ vin)))]
    ; dep= None
    ; body=
        elets
          [("s", call1 "Sign" vin); ("isz", call1 "IsZero" vin)]
          ((f1 -% v "s") *% (f1 -% v "isz")) }

let relu =
  Circuit
    { name= "ReLU"
    ; inputs= [("in", tf)]
    ; outputs= [("out", tfe (toSZ nu =. zmax z0 (toSZ vin)))]
    ; dep= None
    ; body= elet "isp" (call1 "IsPositive" vin) (vin *% v "isp") }

let poly =
  Circuit
    { name= "Poly"
    ; inputs= [("n", tf); ("in", tf)]
    ; outputs= [("out", tfe (nu =. vin *% (vin +% n)))]
    ; dep= None
    ; body= (vin *% vin) +% (n *% vin) }
