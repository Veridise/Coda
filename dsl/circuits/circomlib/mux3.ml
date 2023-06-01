open Ast
open Dsl

let z4 = zn 4

let z8 = zn 8

let c = v "c"

let s = v "s"

let out = v "out"

let t_out = tfq (qeq nu (get c (toUZ (as_le_f s))))

let mux3 =
  Circuit
    { name= "Mux3"
    ; inputs= [("c", tarr_tf z8); ("s", tarr_t_k tf_binary z3)]
    ; outputs= [("out", t_out)]
    ; dep= None
    ; body= f0 }
