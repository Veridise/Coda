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

(* { F | v = in1[0] * in2[0] + ... + in1[k] * in2[k] } *)
let t_ep k =
  tfq
    (qeq nu
       (sum z0 k
          (lama "i" tint (fmul (tget (get ins i) 0) (tget (get ins i) 1))) ) )

(* \i x => x + aux[i] *)
let lam_ep = lama "i" tint (lama "x" tf (fadd x (get aux i)))

let inv_ep i = t_ep i

let escalar_product =
  Circuit
    { name= "EscalarProduct"
    ; inputs= [("w", tnat); ("in1", tarr_tf w); ("in2", tarr_tf w)]
    ; outputs= [("out", t_ep w)]
    ; dep= None
    ; body=
        (* ins = zip in1 in2 *)
        elet "ins" (zip in1 in2)
          (* aux = map (\(i1, i2) => i1 * i2) ins *)
          (elet "aux"
             (map (lama "x" (ttuple [tf; tf]) (fmul (tget x 0) (tget x 1))) ins)
             (* out === iter 0 w lam_ep 0 *)
             (assert_eq out (iter z0 w lam_ep ~init:f0 ~inv:inv_ep)) ) }
