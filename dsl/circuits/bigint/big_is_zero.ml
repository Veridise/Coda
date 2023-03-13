open Ast
open Dsl
open Notation

let vin = v "in"

let vout = v "out"

let x = v "x"

let y = v "y"

let z = v "z"

let n = v "n"

let k = v "k"

let i = v "i"

let a = v "a"

let b = v "b"

let ab = v "ab"

let total = v "total"

let t_k = z_range z1 CPLen

(* BigIsZero *)
let q_biz j = qforall "i" z0 j (qeq (get vin i) f0)

let t_biz = tfq (q_ind_dec nu (q_biz k))

let inv_biz i = tfq (q_ind_dec (eq nu i) (q_biz i))

let lam_biz = lama "i" tint (lama "x" tf (fadd x (call "IsZero" [get vin i])))

let c_big_is_zero =
  Circuit
    { name= "BigIsZero"
    ; inputs= [("k", t_k); ("in", tarr_tf k)]
    ; outputs= [("out", t_biz)]
    ; dep= None
    ; body=
        (* total = (iter 0 k (\i x => x + #IsZero in[i]) 0) *)
        elet "total"
          (iter z0 k lam_biz ~init:f0 ~inv:inv_biz)
          (* out === #IsZero (k - total) *)
          (vout === call "IsZero" [fsub k total]) }
