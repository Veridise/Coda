open Ast
open Dsl

let a = v "a"

let b = v "b"

let c = v "c"

let i = v "i"

let n = v "n"

let s = v "s"

let x = v "x"

let y = v "y"

let z = v "z"

(* { Array<F> | length v = 2 } *)
let tarr_tf_2 = tarr_tf z2

(* { Array<{ Array<F> | length nu = 2 }> | length nu = n } *)
let t_c = tarr_t_k tarr_tf_2 n

(* forall 0 <= i < n, out[i] = (c[i][1] - c[i][0]) * s + c[i][0] *)
let q_mm1 =
  qforall "i" z0 n
    (qeq (get nu i)
       (fadd
          (fmul (fsub (get (get c i) z1) (get (get c i) z0)) s)
          (get (get c i) z0) ) )

let t_mm1 = tarr_t_q_k tf q_mm1 n

let lam_mm1 =
  lama "x" tarr_tf_2
    (ascribe
       (elet "a" (get x z0)
          (elet "b" (get x z1)
             (elet "y" (fsub b a) (elet "z" (fmul y s) (fadd z a))) ) )
       (refine tf
          (qeq nu (fadd (fmul (fsub (get x z1) (get x z0)) s) (get x z0))) ) )

let multi_mux_1 =
  Circuit
    { name= "MultiMux1"
    ; inputs= [("n", tnat); ("c", t_c); ("s", tf)]
    ; outputs= [("out", t_mm1)]
    ; dep= None
    ; body= map lam_mm1 c }
