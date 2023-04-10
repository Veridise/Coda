open Ast
open Dsl
open Notation

let f4 = fn 4

let f8 = fn 8

let z4 = zn 4

let z15 = zn 15

let z32 = zn 32

let z254 = zn 254

let i = v "i"

let n = v "n"

let x = v "x"

let z = v "z"

let vin = v "in"

let out = v "out"

let key = v "KEY"

let n2b = v "n2b"

let n2b0 = v "n2b0"

let n2b1 = v "n2b1"

let n2b2 = v "n2b2"

let n2b3 = v "n2b3"

let rng = v "rng"

let eqs = v "eqs"

let choices = v "choices"

let index = v "index"

let mimc = v "mimc"

(* CalculateTotal *)

let t_ct = tfq (qeq nu (u_sum vin))

let calc_total =
  Circuit
    { name= "CalculateTotal"
    ; inputs= [("n", tnat); ("in", tarr_tf n)]
    ; outputs= [("out", t_ct)]
    ; dep= None
    ; body= make_sum vin ~len:n }

(* QuinSelector *)

let t_choices =
  tfq (qand (lift (z4 <. zsub1 CPLen)) (lift (toUZ nu <. zpow z2 z4)))

let t_index = tfq (lift (toUZ nu <. toUZ choices))

let t_qs =
  tfq (qimply (lift (toUZ index <. toUZ choices)) (nu ==. get vin (toUZ index)))

let quin_selector =
  Circuit
    { name= "QuinSelector"
    ; inputs=
        [ ("choices", t_choices)
        ; ("in", tarr_tf (toUZ choices))
        ; ("index", t_index) ]
    ; outputs= [("out", t_qs)] (* ; outputs= [("out", tunit)] *)
    ; dep= None
    ; body=
        elets
          [("lt", call "LessThan" [z4; index; choices]); ("u0", v "lt" === f1)]
          (elets
             [ ("rng", app (v "gen_rng") (toUZ choices))
             ; ("eqs", map (lama "x" tf (call "IsEqual" [x; index])) rng) ]
             (pairwise_mul vin eqs (fun p ->
                  call "CalculateTotal" [toUZ choices; v p] ) ) ) }

(* IsNegative *)

let t_is_neg = tfq (ind_dec nu (lt (toSZ vin) z0))

let is_neg =
  Circuit
    { name= "IsNegative"
    ; inputs= [("in", tf)]
    ; outputs= [("out", t_is_neg)]
    ; dep= None
    ; body= elet "z" (call2 "Num2Bits" z254 vin) (call1 "Sign" z) }

(* Random *)

let q_lt_232 x = qand (qlt (zn 15) CPrime) (qlt (toUZ x) (zpow z2 z32))

let q_lt_232_arr xs = qforall "i" z0 (len xs) (q_lt_232 (get xs i))

let t_rand = tfq (qand (qleq z0 (toUZ nu)) (qleq (toUZ nu) z15))

let random =
  Circuit
    { name= "Random"
    ; inputs=
        [("in", tarr_t_q_k tf (q_lt_232_arr nu) z3); ("KEY", tfq (q_lt_232 nu))]
    ; outputs= [("out", t_rand)]
    ; dep= None
    ; body=
        elet "mimc"
          (call "MiMCSponge" [z3; z4; z1; vin; key])
          (elet "z" (get mimc z0)
             (elet "n2b"
                (call "Num2Bits" [z254; z])
                (elet "n2b3" (get n2b z3)
                   (elet "n2b2" (get n2b z2)
                      (elet "n2b1" (get n2b z1)
                         (elet "n2b0" (get n2b z0)
                            (* 8 * n2b[3] + 4 * n2b[2] + 2 * n2b[1] + n2b[0] *)
                            (fadd (fmul f8 n2b3)
                               (fadd (fmul f4 n2b2) (fadd (fmul f2 n2b1) n2b0)) ) ) ) ) ) ) )
    }
