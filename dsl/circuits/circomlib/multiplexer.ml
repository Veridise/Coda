open Ast
open Dsl

let i = v "i"

let w = v "w"

let x = v "x"

let in1 = v "in1"

let in2 = v "in2"

let ins = v "ins"

let aux = v "aux"

let out = v "out"

let lam_prod = lama "x" (ttuple [tf; tf]) (fmul (tget x 0) (tget x 1))

(* { F | v = in1[0] * in2[0] + ... + in1[w] * in2[w] } *)
let t_ep = tfq (qeq nu (u_sum (map lam_prod (zip in1 in2))))

let escalar_product =
  Circuit
    { name= "EscalarProduct"
    ; inputs= [("w", tnat); ("in1", tarr_tf w); ("in2", tarr_tf w)]
    ; outputs= [("out", t_ep)]
    ; dep= None
    ; body=
        (* ins = zip in1 in2 *)
        elet "ins" (zip in1 in2)
          (* aux = map (\(i1, i2) => i1 * i2) ins *)
          (elet "aux" (map lam_prod ins) (make_sum aux ~len:w)) }
