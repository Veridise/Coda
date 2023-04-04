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

let rng = v "rng"

let eqs = v "eqs"

let choices = v "choices"

let index = v "index"

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

let t_qs = tfq (qimply (lift (index <. choices)) (nu ==. get vin index))

(* Generates [0; 1; ...; k - 1] *)
let gen_rng k =
  iter z0 k
    (lama "i" tint
       (lama_p
          [("f", tf); ("x", tarr tf)]
          (pair (v "f" +% f1) (concat x (cons (v "f") cnil))) ) )
    ~init:(pair f0 cnil)
    ~inv:(fun i ->
      let j = "jg" in
      (* forall z0 <= j < i, v[j] = ^j *)
      tpair
        (tfe (toUZ nu =. i))
        (tarr_t_q_k tf (qforall j z0 i (get nu (v j) ==. toUZ (v j))) (v j)) )

let quin_selector =
  Circuit
    { name= "QuinSelector"
    ; inputs= [("choices", tf); ("in", tarr_tf (toUZ choices)); ("index", tf)]
    ; outputs= [("out", t_qs)] (* ; outputs= [("out", tunit)] *)
    ; dep= None
    ; body=
        elets
          [("lt", call "LessThan" [z4; index; choices]); ("u0", v "lt" === f1)]
          (elet_p ["_"; "rng"]
             (gen_rng (toUZ choices))
             (elet "eqs"
                (map (lama "x" tf (call "IsEqual" [x; index])) rng)
                (pairwise_mul vin eqs (fun p ->
                     call "CalculateTotal" [toUZ choices; v p] ) ) ) ) }

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
          (call "Num2Bits"
             [z254; get (call "MiMCSponge" [z3; z4; z1; vin; key]) z0] )
          (* 8 * n2b[3] + 4 * n2b[2] + 2 * n2b[1] + n2b[0] *)
          (fadd
             (fmul f8 (get n2b z3))
             (fadd
                (fmul f4 (get n2b z2))
                (fadd (fmul f2 (get n2b z1)) (get n2b z0)) ) ) }
