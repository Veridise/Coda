open Ast
open Dsl
open Notation

(* MerkleTreeInclusionProof *)

let _i = v "_i"

let x = v "x"

let m = v "m"

let c = v "c"

let leaf = v "leaf"

let path_index = v "pathIndex"

let path_elements = v "pathElements"

let depth = v "DEPTH"

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

(* {F | nu = #MrklTreeInclPfHash (zip pathIndex pathElements) leaf } *)
let t_r = tfq (qeq nu (u_hasher (u_zip path_index path_elements) leaf))

(* mrkl_tree_incl_pf (DEPTH : {Z | 0 <= nu }) (leaf : F)
   (pathIndex : { Array<F> | length nu = DEPTH })
   (pathElements : { Array<F> | length nu = DEPTH }) : t_r *)
let mrkl_tree_incl_pf =
  Circuit
    { name= "MerkleTreeInclusionProof"
    ; inputs=
        [ ("DEPTH", tnat)
        ; ("leaf", tf)
        ; ("pathIndex", tarr_tf depth)
        ; ("pathElements", tarr_tf depth) ]
    ; outputs= [("root", t_r)]
    ; dep= None
    ; body= elet "z" (zip path_index path_elements) (hasher z depth leaf) }

let limit_bit_size = v "LIMIT_BIT_SIZE"

let messageId = v "messageId"

let limit = v "limit"

(* a < b <-> out = 1 *)
let t_lt a b = tfq (ind_dec nu (toUZ a <. toUZ b))

let range_check =
  Circuit
    { name= "RangeCheck"
    ; inputs=
        [ ("LIMIT_BIT_SIZE", attaches [lift (nu <. zn 253)] tnat)
        ; ("messageId", tf)
        ; ("limit", tf) ]
    ; outputs= [("rangeCheck", t_lt messageId limit)]
    ; dep= None
    ; body=
        elet "bitCheck"
          (call "Num2Bits" [limit_bit_size; messageId])
          (call "LessThan" [limit_bit_size; messageId; limit]) }
