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

let bits = v "bits"

let max_abs_value = v "max_abs_value"

let lt1 = v "lt1"

let lt2 = v "lt2"

(* CalculateTotal *)

let t_ct = tfq (qeq nu (u_sum vin))

(* calc_total (n : {Z | 0 <= nu }) (in : { Array<F> | length nu = n}) : { F | nu = sum in } *)
let calc_total =
  Circuit
    { name= "CalculateTotal"
    ; inputs= [("n", tnat); ("in", tarr_tf n)]
    ; outputs= [("out", t_ct)]
    ; dep= None
    ; body= make_sum vin ~len:n }

(* QuinSelector *)

(* { F | 4 < C.k - 1 /\ toUZ nu < 2 ^ 4 } *)
let t_choices =
  tfq (qand (lift (z4 <. zsub1 CPLen)) (lift (toUZ nu <. zpow z2 z4)))

(* { F | toUZ nu < toUZ choices } *)
let t_index = tfq (lift (toUZ nu <. toUZ choices))

(* { F | toUZ index < toUZ choices -> nu = in[toUZ index] } *)
let t_qs =
  tfq (qimply (lift (toUZ index <. toUZ choices)) (nu ==. get vin (toUZ index)))

(* quin_selector (choices : t_choices) (in : { Array<F> | length nu = toUZ choices }) (index : t_index) : t_qs *)
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
             (elet "muls"
                (apps (v "pairwise_mul") [toUZ choices; vin; eqs])
                (call "CalculateTotal" [toUZ choices; v "muls"]) ) ) }

(* IsNegative *)

let t_is_neg = tfq (ind_dec nu (lt (toSZ vin) z0))

(* is_neg (in : F) : { F | binary nu /\ nu = 1 -> toSZ in < 0 /\ nu = 0 -> ~(toSZ in < 0) } *)
let is_neg =
  Circuit
    { name= "IsNegative"
    ; inputs= [("in", tf)]
    ; outputs= [("out", t_is_neg)]
    ; dep= None
    ; body= elet "z" (call2 "Num2Bits" z254 vin) (call1 "Sign" z) }

(* Random *)

(* 15 < C.q /\ toUZ x < 2 ^ 32 *)
let q_lt_232 x = qand (qlt (zn 15) CPrime) (qlt (toUZ x) (zpow z2 z32))

(* forall i, 0 <= i < length xs -> q_lt_233 xs[i] *)
let q_lt_232_arr xs = qforall "i" z0 (len xs) (q_lt_232 (get xs i))

(* { F | 0 <= toUZ nu <= 15 } *)
let t_rand = tfq (qleq (toUZ nu) z15)

(* random (in : { Array<F> | q_lt_232_arr nu /\ length nu = 3 }) (KEY : { F | q_lt_232 nu }) : t_rand *)
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
                (* 8 * n2b[3] + 4 * n2b[2] + 2 * n2b[1] + n2b[0] *)
                (fadd
                   (fmul f8 (get n2b z3))
                   (fadd
                      (fmul f4 (get n2b z2))
                      (fadd (fmul f2 (get n2b z1)) (get n2b z0)) ) ) ) ) }

(* RangeProof *)

let t_mav = tfq (lift (z0 <=. toSZ nu))

(* t_rp = { () | numbits(in, bits + 1) /\ numbits(max_abs_value, bits) /\ |in| <= max_abs_value } *)

(* range_proof (bits : { Z | 0 < nu }) (in : F) (max_abs_value : { F | 0 <= toSZ nu }) : t_rp *)
let range_proof =
  Circuit
    { name= "RangeProof"
    ; inputs= [("bits", tpos); ("in", tf); ("max_abs_value", t_mav)]
    ; outputs= []
    ; dep= None
    ; body=
        elet "x"
          (vin +% fpow f2 bits)
          (elet "n2b1"
             (call2 "Num2Bits" (zadd1 bits) x)
             (elet "n2b2"
                (call2 "Num2Bits" bits max_abs_value)
                (elet "lt1"
                   (call "LessThan" [zadd1 bits; max_abs_value +% vin; f0])
                   (elet "u0" (assert_eq lt1 f0)
                      (elet "lt2"
                         (call "LessThan"
                            [ zadd1 bits
                            ; f2 *% max_abs_value
                            ; max_abs_value +% vin ] )
                         (assert_eq lt2 f0) ) ) ) ) ) }

(* MultiRangeProof (broken) *)

let lam_mrp =
  lama "z" tf (elet "_y" (call "RangeProof" [bits; z; max_abs_value]) f0)

let multi_range_proof =
  Circuit
    { name= "MultiRangeProof"
    ; inputs=
        [ ("n", tnat)
        ; ("bits", tpos)
        ; ("in", tarr_tf n)
        ; ("max_abs_value", t_mav) ]
    ; outputs= []
    ; dep= None
    ; body= elet "_x" (map lam_mrp vin) unit_val }
