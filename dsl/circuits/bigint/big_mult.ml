open Ast
open Dsl
open Notation

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

(* { Z | 0 <= v /\ 2 * v <= C.k } *)
let t_n = attach (lift (z2 *! nu <. CPLen)) tnat

let mod_prod =
  Circuit
    { name= "ModProd"
    ; inputs= [("n", t_n); ("a", tf); ("b", tf)]
    ; outputs=
        [("prod", attach (lift (toUZ nu <=. (z2 ^! n) -! z1)) tf); ("carry", tf)]
    ; (* carry * 2 ^ n + prod = a * b *)
      dep= Some ((carry *% (f2 ^% n)) +% prod ==. a *% b)
    ; body=
        (* n2b = #Num2Bits (2 * n) (a * b) *)
        (* prod === #Bits2Num n (take n2b n) *)
        elets
          [ ("n2b", call "Num2Bits" [z2 *. n; a *% b])
          ; ("prod", call "Bits2Num" [n; take n2b n])
          ; (* carry === #Bits2Num n (drop n n2b) *)
            ("carry", call "Bits2Num" [n; drop n2b n]) ]
          (pair prod carry) }

let lam_pts = lama "i" tint (lama "x" (tarr_tf i) (concat x (cons i cnil)))

(* TODO: Decide whether this is sufficient *)
let inv_pts i = tarr_tf i

let lam_eval_poly z x =
  lama "i" tint (lama "y" tf (fadd y (fmul (get z i) (fpow x i))))

(* Compute z(x) = z[0] + z[1] * x + z[2] * x^2 + ... + z[k-1] * x^(k-1) *)
let rec eval_poly k =
  lama "z" (tarr_tf k)
    (lama "x" tf
       (iter z0 k (lam_eval_poly z x) ~init:f0 ~inv:(fun i ->
            tfq (qeq nu (app (app (eval_poly i) (take i z)) x)) ) ) )

let big_mult_short_long =
  Circuit
    { name= "BigMultShortLong"
    ; inputs=
        [ ("n", tnat)
        ; ("k", tpos)
        ; ("m_out", tnat)
        ; ("a", tarr_tf k)
        ; ("b", tarr_tf k) ]
        (* TODO: Add real output type *)
    ; outputs= [("out", tarr_tf (zsub1 (zmul z2 k)))]
    ; dep= None
    ; body=
        (* k2 = 2k - 1*)
        elet "k2"
          (zsub1 (zmul z2 k))
          (* out = [*; *; ...; *] *)
          (elet "out" (Liblam.stars k2)
             (* pts = iter 0 k2 (\i v => v ++ [i]) [] *)
             (elet "pts"
                (iter z0 k2 lam_pts ~init:cnil ~inv:inv_pts)
                (* out_pts = map (eval_poly k2 out) pts *)
                (elet "out_pts"
                   (map (lama "x" tf (app (app (eval_poly k2) out) x)) pts)
                   (* a_pts = map (eval_poly k a) pts *)
                   (elet "a_pts"
                      (map (lama "x" tf (app (app (eval_poly k) a) x)) pts)
                      (* b_pts = map (eval_poly k b) pts *)
                      (elet "b_pts"
                         (map (lama "x" tf (app (app (eval_poly k) b) x)) pts)
                         (* ab_pts = zip a_pts b_pts *)
                         (elet "ab_pts" (zip a_pts b_pts)
                            (* axb_pts = map (\(a, b) => a * b) ab_pts *)
                            (elet "axb_pts"
                               (map
                                  (lama "x"
                                     (ttuple [tf; tf])
                                     (fmul (tget x 0) (tget x 1)) )
                                  ab_pts )
                               (* out_pts === axb_pts *)
                               (assert_eq out_pts axb_pts) ) ) ) ) ) ) ) }

(* { F | ^v <= 2^n - 1 } *)

let tf_n_bit = tfe (toUZ nu <=. (z2 ^! n) -! z1)

(* { F | ^v <= C.k - 1 } *)
let t_n = attaches [lift (nu <=. CPLen -! z1); lift (z1 <=. nu)] tnat

(* Proper big Ints of length k *)
let t_big_int k = tarr_t_k tf_n_bit k

let big_mult =
  Circuit
    { name= "BigMult"
    ; inputs= [("n", tnat); ("k", tpos); ("a", t_big_int k); ("b", t_big_int k)]
    ; outputs=
        [ ( "out"
          , tarr_t_q_k tf_n_bit
              (as_le n nu ==. as_le n a *. as_le n b)
              (zmul z2 k) ) ]
    ; dep= None
    ; body= consts_n (zmul z2 k) f0 }
