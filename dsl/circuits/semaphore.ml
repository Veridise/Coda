open Ast
open Dsl
open Typecheck

let n = v "n"

let a = v "a"

let b = v "b"

let c = v "c"

let s = v "s"

let x = v "x"

let out = v "out"

(* { Array<F> | length v = 2 } *)
let tarr_tf_2 = tarr_t_k tf z2

(* { Array<{ Array<F> | length nu = 2 }> | length nu = n } *)
let t_c = tarr_t_k tarr_tf_2 n

(* TODO: Add correct type *)
let t_out = tarr_t_k tf n

let lam_mm1 =
  lama "x" tarr_tf_2
    (elet "a" (get x z0) (elet "b" (get x z1) (fadd (fmul (fsub b a) s) a)))

let multi_mux_1 =
  Circuit
    { name= "MultiMux1"
    ; inputs= [("n", tnat); ("c", t_c); ("s", tf)]
    ; outputs= [("out", t_out)]
    ; dep= None
    ; body=
        (* out === map (\[a; b] => (b - a) * s + a) c *)
        assert_eq out (map lam_mm1 c) }

let check_multi_mux_1 = typecheck_circuit d_empty multi_mux_1
