open Ast
open Dsl
open Typecheck

let n = v "n"

let a = v "a"

let b = v "b"

let c = v "c"

let i = v "i"

let j = v "j"

let s = v "s"

let x = v "x"

let z = v "z"

let out = v "out"

let nLevels = v "nLevels"

let pathIndices = v "pathIndices"

let siblings = v "siblings"

let root = v "root"

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

(* TODO: Add real type of root *)
let t_r = tf

let lam_mtip =
  lama "i" tint
    (lama "x" tf
       (elet "j"
          (tget (get z i) 0)
          (elet "s"
             (tget (get z i) 1)
             (elet "u0"
                (* pathIndices[i] binary *)
                (assert_eq (fmul j (fsub f1 j)) f0)
                (elet "c"
                   (cons
                      (cons x (cons s cnil))
                      (cons (cons s (cons x cnil)) cnil) )
                   (call "Poseidon" [z2; call "MultiMux1" [z2; c; j]]) ) ) ) ) )

(* TODO: Add real invariant *)
let inv_mtip _ = tf

let mrkl_tree_incl_pf =
  Circuit
    { name= "MerkleTreeInclusionProof"
    ; inputs=
        [ ("nLevels", tnat)
        ; ("leaf", tf)
        ; ("pathIndices", tarr_tf nLevels)
        ; ("siblings", tarr_tf nLevels) ]
    ; outputs= [("root", t_r)]
    ; dep= None
    ; body=
        elet "z" (zip pathIndices siblings)
          (assert_eq root (iter z0 nLevels lam_mtip leaf inv_mtip)) }
