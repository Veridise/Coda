open Ast
open Dsl
open Typecheck

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

let rng = v "rng"

let eqs = v "eqs"

let choices = v "choices"

let index = v "index"

(* CalculateTotal *)

let lam_sum_arr xs = lama "i" tint (lama "x" tf (fadd x (get xs i)))

let rec sum_arr xs =
  iter z0 (len xs) (lam_sum_arr xs) ~init:f0 ~inv:(fun i ->
      tfq (qeq nu (sum_arr (take i xs))) )

let t_ct = tfq (qeq nu (sum_arr vin))

let calc_total =
  Circuit
    { name= "CalculateTotal"
    ; inputs= [("n", tnat); ("in", tarr_tf n)]
    ; outputs= [("out", t_ct)]
    ; dep= None
    ; body= sum_arr vin }

let check_calc_total = typecheck_circuit d_empty calc_total

(* QuinSelector *)

let t_qs = tfq (qimply (qlt index choices) (qeq nu (get vin index)))

let lam_rng = lama "i" tint (lama "x" (tarr_tf i) (concat x (cons i cnil)))

(* Generates [0; 1; ...; k - 1] *)
let rec gen_rng k =
  iter z0 k lam_rng ~init:cnil ~inv:(fun i -> tarr_t_q tf (qeq nu (gen_rng i)))

(* map (\(a, b) => a * b) z *)
let pair_mul z = map (lama "x" (tpair tf tf) (fmul (tget x 0) (tget x 1))) z

let quin_selector =
  Circuit
    { name= "QuinSelector"
    ; inputs= [("choices", tnat); ("in", tarr_tf choices); ("index", tf)]
    ; outputs= [("out", t_qs)]
    ; dep= None
    ; body=
        elet "u0"
          (assert_eq (call "LessThan" [z4; cons index (cons choices cnil)]) f1)
          (elet "rng" (gen_rng choices)
             (elet "eqs"
                (map (lama "x" tf (call "IsEqual" [x; index])) rng)
                (elet "z" (zip vin eqs)
                   (call "CalculateTotal" [choices; pair_mul z]) ) ) ) }

(* IsNegative *)

(* TODO: Need integer division to specify this correctly *)
let t_is_neg = tf

let is_neg =
  Circuit
    { name= "IsNegative"
    ; inputs= [("in", tf)]
    ; outputs= [("out", t_is_neg)]
    ; dep= None
    ; body= call "Sign" [call "Num2Bits" [z254; vin]] }

(* Random *)

let q_lt_232 x = qlt (toUZ x) (zpow z2 z32)

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
        elet "n2b"
          (call "Num2Bits" [z254; call "MiMCSponge" [z3; z4; z1; vin; key]])
          (* 8 * n2b[3] + 4 * n2b[2] + 2 * n2b[1] + n2b[0] *)
          (fadd
             (fmul f8 (get n2b z3))
             (fadd
                (fmul f4 (get n2b z2))
                (fadd (fmul f2 (get n2b z1)) (get n2b z0)) ) ) }
