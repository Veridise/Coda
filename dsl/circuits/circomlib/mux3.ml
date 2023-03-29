open Ast
open Dsl

let z4 = zn 4

let z8 = zn 8

let c = v "c"

let s = v "s"

let out = v "out"

(* out = c[|#Bits2Num 3 s|] *)
let t_out = tfq (qeq nu (get c (toUZ (call "Bits2Num" [z3; s]))))

let mux3 =
  Circuit
    { name= "Mux3"
    ; inputs= [("c", tarr_tf z8); ("s", tarr_t_k tf_binary z3)]
    ; outputs= [("out", t_out)]
    ; dep= None
    ; body= star }
