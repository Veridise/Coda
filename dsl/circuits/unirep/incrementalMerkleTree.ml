open Ast
open Dsl

(* MerkleTreeInclusionProof *)

let _i = v "_i"

let x = v "x"

let m = v "m"

let c = v "c"

let n_levels = v "n_levels"

let leaf = v "leaf"

let path_index = v "path_index"

let path_elements = v "path_elements"

let z = v "z"

let u_hasher z init = unint "MrklTreeInclPfHash" [z; init]

let u_zip xs ys = unint "zip" [xs; ys]

let z_i_0 z = tget (get z _i) 0

let z_i_1 z = tget (get z _i) 1

let lam_mtip z =
  lama "_i" tint
    (lama "x" tf
       (elet "u0"
          (* path_index[i] binary *)
          (assert_eq (fmul (z_i_0 z) (fsub f1 (z_i_0 z))) f0)
          (elet "c"
             (const_array (tarr_tf z2)
                [const_array tf [x; z_i_1 z]; const_array tf [z_i_1 z; x]] )
             (elet "m"
                (call "MultiMux1" [z2; c; z_i_0 z])
                (call "Poseidon" [z2; m]) ) ) ) )

let hasher z len init =
  iter z0 len (lam_mtip z) ~init ~inv:(fun i ->
      tfq (qeq nu (u_hasher (u_take i z) init)) )

(* {F | nu = #MrklTreeInclPfHash (zip pathIndices siblings) leaf } *)
let t_r = tfq (qeq nu (u_hasher (u_zip path_index path_elements) leaf))

(* mrkl_tree_incl_pf (nLevels : {Z | 0 <= nu }) (leaf : F)
   (pathIndices : { Array<F> | length nu = nLevels })
   (siblings : { Array<F> | length nu = nLevels }) : t_r *)
let mrkl_tree_incl_pf =
  Circuit
    { name= "MerkleTreeInclusionProof"
    ; inputs=
        [ ("n_levels", tnat)
        ; ("leaf", tf)
        ; ("path_index", tarr_tf n_levels)
        ; ("path_elements", tarr_tf n_levels) ]
    ; outputs= [("root", t_r)]
    ; dep= None
    ; body= elet "z" (zip path_index path_elements) (hasher z n_levels leaf) }
