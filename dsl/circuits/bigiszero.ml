open Ast
open Dsl

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
          (assert_eq vout (call "IsZero" [fsub k total])) }

(* BigIsEqual *)
let q_bie j = qforall "i" z0 j (qeq (get a i) (get b i))

let t_bie = tfq (q_ind_dec nu (q_bie k))

let inv_bie i = tfq (q_ind_dec (eq nu i) (q_bie i))

let lam_bie =
  lama "i" tint
    (lama "x" tf
       (fadd x (call "IsEqual" [tget (get ab i) 0; tget (get ab i) 1])) )

let c_big_is_equal =
  Circuit
    { name= "BigIsEqual"
    ; inputs= [("k", t_k); ("a", tarr_tf k); ("b", tarr_tf k)]
    ; outputs= [("out", t_bie)]
    ; dep= None
    ; body=
        (* ab = zip a b *)
        elet "ab" (zip a b)
          (* total = (iter 0 k (\i x => x + #IsEqual ab[i].0 ab[i].1) 0) *)
          (elet "total"
             (iter z0 k lam_bie ~init:f0 ~inv:inv_bie)
             (* out === #IsZero (k - total) *)
             (assert_eq vout (call "IsZero" [fsub k total])) ) }
