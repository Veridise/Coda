open Ast
open Dsl
open Typecheck

let z4 = zn 4

let i = v "i"

let n = v "n"

let x = v "x"

let z = v "z"

let vin = v "in"

let out = v "out"

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
