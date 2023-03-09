open Ast
open Dsl
open Typecheck
open Bitify

let n = v "n"

let k = v "k"

let k2 = v "k2"

let a = v "a"

let b = v "b"

let i = v "i"

let x = v "x"

let y = v "y"

let z = v "z"

let out = v "out"

let ei = v "ei"

let pi = v "pi"

let n2b = v "n2b"

let prod = v "prod"

let carry = v "carry"

let pts = v "pts"

let a_pts = v "a_pts"

let b_pts = v "b_pts"

let ab_pts = v "ab_pts"

let axb_pts = v "axb_pts"

let out_pts = v "out_pts"

let t_arr_tf k = tarr tf QTrue k

(* { Z | 0 <= v /\ 2 * v <= C.k } *)
let t_n = TRef (TInt, qand (QExpr (leq z0 nu)) (QExpr (leq (zmul z2 nu) CPLen)))

let mod_prod =
  Circuit
    { name= "ModProd"
    ; inputs= [("n", t_n); ("a", tf); ("b", tf)]
    ; outputs= [("prod", tf); ("carry", tf)]
    ; (* carry * 2 ^ n + prod = a * b *)
      dep= Some (qeq (fadd (fmul carry (fpow f2 n)) prod) (fmul a b))
    ; body=
        [ (* n2b = #Num2Bits (2 * n) (a * b) *)
          slet "n2b" (call "Num2Bits" [zmul z2 n; fmul a b])
        ; (* prod === #Bits2Num n (take n n2b) *)
          assert_eq prod (call "Bits2Num" [n; take n n2b])
        ; (* carry === #Bits2Num n (drop n n2b) *)
          assert_eq carry (call "Bits2Num" [n; drop n n2b]) ] }

let deltas_mp = add_to_deltas d_empty [num2bits; bits2num]

let check_mod_prod = typecheck_circuit deltas_mp mod_prod

let lam_pts = lama "i" tint (lama "x" (t_arr_tf i) (concat x (cons i cnil)))

(* TODO: Decide whether this is sufficient *)
let inv_pts i _ = t_arr_tf i

let lam_eval_poly z x =
  lama "i" tint (lama "y" tf (fadd y (fmul (get z i) (fpow x i))))

(* Compute z(x) = z[0] + z[1] * x + z[2] * x^2 + ... + z[k-1] * x^(k-1) *)
let rec eval_poly k =
  lama "z" (t_arr_tf k)
    (lama "x" tf
       (iter z0 k (lam_eval_poly z x) f0 (fun i _ ->
            tfq (qeq nu (app (app (eval_poly i) (take i z)) x)) ) ) )

let big_mult_short_long =
  Circuit
    { name= "BigMultShortLong"
    ; inputs=
        [ ("n", tnat)
        ; ("k", tpos)
        ; ("m_out", tnat)
        ; ("a", t_arr_tf k)
        ; ("b", t_arr_tf k) ]
        (* TODO: Add real output type *)
    ; outputs= [("out", t_arr_tf (zsub1 (zmul z2 k)))]
    ; dep= None
    ; body=
        [ (* k2 = 2k - 1*)
          slet "k2" (zsub1 (zmul z2 k))
        ; (* out = [*; *; ...; *] *)
          slet "out" (stars k2)
        ; (* pts = iter 0 k2 (\i v => v ++ [i]) [] *)
          slet "pts" (iter z0 k2 lam_pts cnil inv_pts)
        ; (* out_pts = map (eval_poly k2 out) pts *)
          slet "out_pts"
            (map (lama "x" tf (app (app (eval_poly k2) out) x)) pts)
        ; (* a_pts = map (eval_poly k a) pts *)
          slet "a_pts" (map (lama "x" tf (app (app (eval_poly k) a) x)) pts)
        ; (* b_pts = map (eval_poly k b) pts *)
          slet "b_pts" (map (lama "x" tf (app (app (eval_poly k) b) x)) pts)
        ; (* ab_pts = zip a_pts b_pts *)
          slet "ab_pts" (zip a_pts b_pts)
        ; (* axb_pts = map (\(a, b) => a * b) ab_pts *)
          slet "axb_pts"
            (map
               (lama "x" (ttuple [tf; tf]) (fmul (tget x 0) (tget x 1)))
               ab_pts )
        ; (* out_pts === axb_pts *)
          assert_eq out_pts axb_pts ] }
