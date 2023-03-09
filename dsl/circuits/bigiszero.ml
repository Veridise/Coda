open Ast
open Dsl
open Typecheck

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

(* BigIsZero *)
let q_biz j = qforall "i" z0 j (qeq (get vin i) f0)

let t_biz = tfq (q_ind_dec nu (q_biz k))

let inv_biz i x = tfq (q_ind_dec (eq x i) (q_biz i))

let lam_biz = lama "i" tint (lama "x" tf (fadd x (call "IsZero" [get vin i])))

let c_big_is_zero =
  Circuit
    { name= "BigIsZero"
    ; inputs= [("k", t_k); ("in", t_arr_tf k)]
    ; outputs= [("out", t_biz)]
    ; dep= None
    ; body=
        [ (* total = (iter 0 k (\i x => x + #IsZero in[i]) 0) *)
          slet "total" (iter z0 k lam_biz f0 inv_biz)
        ; (* out === #IsZero (k - total) *)
          assert_eq vout (call "IsZero" [fsub k total]) ] }

let check_big_is_zero =
  typecheck_circuit (add_to_delta d_empty c_is_zero) c_big_is_zero

(* BigIsEqual *)
let q_bie j = qforall "i" z0 j (qeq (get a i) (get b i))

let t_bie = tfq (q_ind_dec nu (q_bie k))

let inv_bie i x = tfq (q_ind_dec (eq x i) (q_bie i))

let lam_bie =
  lama "i" tint
    (lama "x" tf
       (fadd x (call "IsEqual" [tget (get ab i) 0; tget (get ab i) 1])) )

let c_big_is_equal =
  Circuit
    { name= "BigIsEqual"
    ; inputs= [("k", t_k); ("a", t_arr_tf k); ("b", t_arr_tf k)]
    ; outputs= [("out", t_bie)]
    ; dep= None
    ; body=
        [ (* ab = zip a b *)
          slet "ab" (zip a b)
        ; (* total = (iter 0 k (\i x => x + #IsEqual ab[i].0 ab[i].1) 0) *)
          slet "total" (iter z0 k lam_bie f0 inv_bie)
        ; (* out === #IsZero (k - total) *)
          assert_eq vout (call "IsZero" [fsub k total]) ] }

let check_big_is_equal =
  typecheck_circuit
    (add_to_deltas d_empty [c_is_equal; c_is_zero])
    c_big_is_equal
