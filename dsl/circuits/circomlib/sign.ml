open Ast
open Dsl

let z254 = zn 254

let vin = v "in"

let t_sign = tfq (ind_dec nu (lt (toSZ (call "Bits2Num" [z254; vin])) z0))

let c_sign =
  Circuit
    { name= "Sign"
    ; inputs= [("in", tarr_t_k tf_binary z254)]
    ; outputs= [("out", t_sign)]
    ; dep= None
    ; body= star }
