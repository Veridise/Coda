open Ast
open Dsl
open Nice_dsl
open Expr

(* open Qual *)
open Typ
(* open TypRef *)

(* Included from `semaphore.ml` *)

let identityNullifier = v "identityNullifier"

let externalNullifier = v "externalNullifier"

let u_calc_null_hash x y = unint "CalculateNullifierHash" [x; y]

(* { F | nu =  #CalculateNullifierHash externalNullifier identityNullifier } *)
let t_semaphore_null_hash_qual =
  qeq nu (u_calc_null_hash externalNullifier identityNullifier)

let identityNullifier = v "identityNullifier"

let identityTrapdoor = v "identityTrapdoor"

let t_semaphore_null_hash = tfq t_semaphore_null_hash_qual

let u_calc_id_commit x = unint "CalculateIdentityCommitment" [x]

let u_calc_secret x y = unint "CalculateSecret" [x; y]

let u_calc_null_hash x y = unint "CalculateNullifierHash" [x; y]

let u_mrkl_tree_incl_pf xs i s = unint "MerkleTreeInclusionProof" [xs; i; s]

(* { F | nu = #MerkleTreeInclusionProof
         (#CalculateIdentityCommitment (#CalculateSecret identityNullifier identityTrapdoor))
         treePathIndices treeSiblings } *)
let t_semaphore_root_qual treePathIndices treeSiblings =
  qeq nu
    (u_mrkl_tree_incl_pf
       (u_calc_id_commit (u_calc_secret identityNullifier identityTrapdoor))
       treePathIndices treeSiblings )

let t_semaphore_root treePathIndices treeSiblings =
  tfq (t_semaphore_root_qual treePathIndices treeSiblings)

(* Circom->Coda *)
let body_Ark (out_0, out_1, out_2, in_0, in_1, in_2) body =
  elet out_0 star @@ elet out_1 star @@ elet out_2 star @@ elet in_0 star
  @@ elet in_1 star @@ elet in_2 star @@ body

let body_Sigma (out, in_, in2, in4) body =
  elet out star @@ elet in_ star @@ elet in2 star @@ elet in4 star @@ body

let body_Mix (out_0, out_1, out_2, in_0, in_1, in_2) body =
  elet out_0 star @@ elet out_1 star @@ elet out_2 star @@ elet in_0 star
  @@ elet in_1 star @@ elet in_2 star @@ body

let body_MixS (out_0, out_1, out_2, in_0, in_1, in_2) body =
  elet out_0 star @@ elet out_1 star @@ elet out_2 star @@ elet in_0 star
  @@ elet in_1 star @@ elet in_2 star @@ body

let body_MixLast (out, in_0, in_1, in_2) body =
  elet out star @@ elet in_0 star @@ elet in_1 star @@ elet in_2 star @@ body

let body_PoseidonEx (out_0, inputs_0, inputs_1, initialState) body =
  elet out_0 star @@ elet inputs_0 star @@ elet inputs_1 star
  @@ elet initialState star @@ body

let body_Poseidon (out, inputs_0, inputs_1) body =
  elet out star @@ elet inputs_0 star @@ elet inputs_1 star @@ body

let body_CalculateSecret (out, identityNullifier, identityTrapdoor) body =
  elet "poseidon_inputs_0" (var identityNullifier)
  @@ elet "poseidon_inputs_1" (var identityTrapdoor)
  @@ body_Poseidon ("poseidon_out", "poseidon_inputs_0", "poseidon_inputs_1")
  @@ elet out (var "poseidon_out")
  @@ body

let circuit_CalculateSecret =
  Circuit
    { name= "CalculateSecret"
    ; inputs= [("identityNullifier", field); ("identityTrapdoor", field)]
    ; outputs= [("out", field)]
    ; dep= None
    ; body=
        body_CalculateSecret
          ("out", "identityNullifier", "identityTrapdoor")
          (Expr.tuple [var "out"]) }

let body_CalculateIdentityCommitment (out, secret) body =
  elet "poseidon_inputs_0" (var secret)
  @@ body_Poseidon ("poseidon_out", "poseidon_inputs_1", "poseidon_inputs_0")
  @@ elet out (var "poseidon_out")
  @@ body

let circuit_CalculateIdentityCommitment =
  Circuit
    { name= "CalculateIdentityCommitment"
    ; inputs= [("secret", field)]
    ; outputs= [("out", field)]
    ; dep= None
    ; body=
        body_CalculateIdentityCommitment ("out", "secret")
          (Expr.tuple [var "out"]) }

let body_CalculateNullifierHash (out, externalNullifier, identityNullifier) body
    =
  elet "poseidon_inputs_0" (var externalNullifier)
  @@ elet "poseidon_inputs_1" (var identityNullifier)
  @@ body_Poseidon ("poseidon_out", "poseidon_inputs_0", "poseidon_inputs_1")
  @@ elet out (var "poseidon_out")
  @@ body

let circuit_CalculateNullifierHash =
  Circuit
    { name= "CalculateNullifierHash"
    ; inputs= [("externalNullifier", field); ("identityNullifier", field)]
    ; outputs= [("out", field)]
    ; dep= None
    ; body=
        body_CalculateNullifierHash
          ("out", "externalNullifier", "identityNullifier")
          (Expr.tuple [var "out"]) }

let body_MultiMux1 (out_0, out_1, c_0_0, c_0_1, c_1_0, c_1_1, s) body =
  elet "var_0_1" (F.const 2)
  @@ elet "var_1_1" (F.const 0)
  @@ elet out_0 F.(F.(F.(var c_0_1 - var c_0_0) * var s) + var c_0_0)
  @@ elet "var_1_2" (F.const 0)
  @@ elet out_1 F.(F.(F.(var c_1_1 - var c_1_0) * var s) + var c_1_0)
  @@ elet "var_1_3" (F.const 0)
  @@ body

let circuit_MultiMux1 =
  Circuit
    { name= "MultiMux1"
    ; inputs=
        [ ("c_0_0", field)
        ; ("c_0_1", field)
        ; ("c_1_0", field)
        ; ("c_1_1", field)
        ; ("s", field) ]
    ; outputs= [("out_0", field); ("out_1", field)]
    ; dep= None
    ; body=
        body_MultiMux1
          ("out_0", "out_1", "c_0_0", "c_0_1", "c_1_0", "c_1_1", "s")
          (Expr.tuple [var "out_0"; var "out_1"]) }

let body_MerkleTreeInclusionProof
    ( root
    , leaf
    , pathIndices_0
    , pathIndices_1
    , pathIndices_2
    , pathIndices_3
    , pathIndices_4
    , pathIndices_5
    , pathIndices_6
    , pathIndices_7
    , pathIndices_8
    , pathIndices_9
    , pathIndices_10
    , pathIndices_11
    , pathIndices_12
    , pathIndices_13
    , pathIndices_14
    , pathIndices_15
    , pathIndices_16
    , pathIndices_17
    , pathIndices_18
    , pathIndices_19
    , siblings_0
    , siblings_1
    , siblings_2
    , siblings_3
    , siblings_4
    , siblings_5
    , siblings_6
    , siblings_7
    , siblings_8
    , siblings_9
    , siblings_10
    , siblings_11
    , siblings_12
    , siblings_13
    , siblings_14
    , siblings_15
    , siblings_16
    , siblings_17
    , siblings_18
    , siblings_19
    , hashes_0
    , hashes_1
    , hashes_2
    , hashes_3
    , hashes_4
    , hashes_5
    , hashes_6
    , hashes_7
    , hashes_8
    , hashes_9
    , hashes_10
    , hashes_11
    , hashes_12
    , hashes_13
    , hashes_14
    , hashes_15
    , hashes_16
    , hashes_17
    , hashes_18
    , hashes_19
    , hashes_20 ) body =
  elet "var_0_1" (F.const 20)
  @@ elet hashes_0 (var leaf)
  @@ elet "var_1_1" (F.const 0)
  @@ assert_eq_in "_assertion_1"
       F.(var pathIndices_0 * F.(F.const 1 - var pathIndices_0))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_0)
  @@ elet "mux_c_0_1" (var siblings_0)
  @@ elet "mux_c_1_0" (var siblings_0)
  @@ elet "mux_c_1_1" (var hashes_0)
  @@ elet "mux_s" (var pathIndices_0)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_1 (var "poseidons_out")
  @@ elet "var_1_2" (F.const 0)
  @@ assert_eq_in "_assertion_2"
       F.(var pathIndices_1 * F.(F.const 1 - var pathIndices_1))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_1)
  @@ elet "mux_c_0_1" (var siblings_1)
  @@ elet "mux_c_1_0" (var siblings_1)
  @@ elet "mux_c_1_1" (var hashes_1)
  @@ elet "mux_s" (var pathIndices_1)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_2 (var "poseidons_out")
  @@ elet "var_1_3" (F.const 0)
  @@ assert_eq_in "_assertion_3"
       F.(var pathIndices_2 * F.(F.const 1 - var pathIndices_2))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_2)
  @@ elet "mux_c_0_1" (var siblings_2)
  @@ elet "mux_c_1_0" (var siblings_2)
  @@ elet "mux_c_1_1" (var hashes_2)
  @@ elet "mux_s" (var pathIndices_2)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_3 (var "poseidons_out")
  @@ elet "var_1_4" (F.const 0)
  @@ assert_eq_in "_assertion_4"
       F.(var pathIndices_3 * F.(F.const 1 - var pathIndices_3))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_3)
  @@ elet "mux_c_0_1" (var siblings_3)
  @@ elet "mux_c_1_0" (var siblings_3)
  @@ elet "mux_c_1_1" (var hashes_3)
  @@ elet "mux_s" (var pathIndices_3)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_4 (var "poseidons_out")
  @@ elet "var_1_5" (F.const 0)
  @@ assert_eq_in "_assertion_5"
       F.(var pathIndices_4 * F.(F.const 1 - var pathIndices_4))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_4)
  @@ elet "mux_c_0_1" (var siblings_4)
  @@ elet "mux_c_1_0" (var siblings_4)
  @@ elet "mux_c_1_1" (var hashes_4)
  @@ elet "mux_s" (var pathIndices_4)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_5 (var "poseidons_out")
  @@ elet "var_1_6" (F.const 0)
  @@ assert_eq_in "_assertion_6"
       F.(var pathIndices_5 * F.(F.const 1 - var pathIndices_5))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_5)
  @@ elet "mux_c_0_1" (var siblings_5)
  @@ elet "mux_c_1_0" (var siblings_5)
  @@ elet "mux_c_1_1" (var hashes_5)
  @@ elet "mux_s" (var pathIndices_5)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_6 (var "poseidons_out")
  @@ elet "var_1_7" (F.const 0)
  @@ assert_eq_in "_assertion_7"
       F.(var pathIndices_6 * F.(F.const 1 - var pathIndices_6))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_6)
  @@ elet "mux_c_0_1" (var siblings_6)
  @@ elet "mux_c_1_0" (var siblings_6)
  @@ elet "mux_c_1_1" (var hashes_6)
  @@ elet "mux_s" (var pathIndices_6)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_7 (var "poseidons_out")
  @@ elet "var_1_8" (F.const 0)
  @@ assert_eq_in "_assertion_8"
       F.(var pathIndices_7 * F.(F.const 1 - var pathIndices_7))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_7)
  @@ elet "mux_c_0_1" (var siblings_7)
  @@ elet "mux_c_1_0" (var siblings_7)
  @@ elet "mux_c_1_1" (var hashes_7)
  @@ elet "mux_s" (var pathIndices_7)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_8 (var "poseidons_out")
  @@ elet "var_1_9" (F.const 0)
  @@ assert_eq_in "_assertion_9"
       F.(var pathIndices_8 * F.(F.const 1 - var pathIndices_8))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_8)
  @@ elet "mux_c_0_1" (var siblings_8)
  @@ elet "mux_c_1_0" (var siblings_8)
  @@ elet "mux_c_1_1" (var hashes_8)
  @@ elet "mux_s" (var pathIndices_8)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_9 (var "poseidons_out")
  @@ elet "var_1_10" (F.const 0)
  @@ assert_eq_in "_assertion_10"
       F.(var pathIndices_9 * F.(F.const 1 - var pathIndices_9))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_9)
  @@ elet "mux_c_0_1" (var siblings_9)
  @@ elet "mux_c_1_0" (var siblings_9)
  @@ elet "mux_c_1_1" (var hashes_9)
  @@ elet "mux_s" (var pathIndices_9)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_10 (var "poseidons_out")
  @@ elet "var_1_11" (F.const 0)
  @@ assert_eq_in "_assertion_11"
       F.(var pathIndices_10 * F.(F.const 1 - var pathIndices_10))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_10)
  @@ elet "mux_c_0_1" (var siblings_10)
  @@ elet "mux_c_1_0" (var siblings_10)
  @@ elet "mux_c_1_1" (var hashes_10)
  @@ elet "mux_s" (var pathIndices_10)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_11 (var "poseidons_out")
  @@ elet "var_1_12" (F.const 0)
  @@ assert_eq_in "_assertion_12"
       F.(var pathIndices_11 * F.(F.const 1 - var pathIndices_11))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_11)
  @@ elet "mux_c_0_1" (var siblings_11)
  @@ elet "mux_c_1_0" (var siblings_11)
  @@ elet "mux_c_1_1" (var hashes_11)
  @@ elet "mux_s" (var pathIndices_11)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_12 (var "poseidons_out")
  @@ elet "var_1_13" (F.const 0)
  @@ assert_eq_in "_assertion_13"
       F.(var pathIndices_12 * F.(F.const 1 - var pathIndices_12))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_12)
  @@ elet "mux_c_0_1" (var siblings_12)
  @@ elet "mux_c_1_0" (var siblings_12)
  @@ elet "mux_c_1_1" (var hashes_12)
  @@ elet "mux_s" (var pathIndices_12)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_13 (var "poseidons_out")
  @@ elet "var_1_14" (F.const 0)
  @@ assert_eq_in "_assertion_14"
       F.(var pathIndices_13 * F.(F.const 1 - var pathIndices_13))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_13)
  @@ elet "mux_c_0_1" (var siblings_13)
  @@ elet "mux_c_1_0" (var siblings_13)
  @@ elet "mux_c_1_1" (var hashes_13)
  @@ elet "mux_s" (var pathIndices_13)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_14 (var "poseidons_out")
  @@ elet "var_1_15" (F.const 0)
  @@ assert_eq_in "_assertion_15"
       F.(var pathIndices_14 * F.(F.const 1 - var pathIndices_14))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_14)
  @@ elet "mux_c_0_1" (var siblings_14)
  @@ elet "mux_c_1_0" (var siblings_14)
  @@ elet "mux_c_1_1" (var hashes_14)
  @@ elet "mux_s" (var pathIndices_14)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_15 (var "poseidons_out")
  @@ elet "var_1_16" (F.const 0)
  @@ assert_eq_in "_assertion_16"
       F.(var pathIndices_15 * F.(F.const 1 - var pathIndices_15))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_15)
  @@ elet "mux_c_0_1" (var siblings_15)
  @@ elet "mux_c_1_0" (var siblings_15)
  @@ elet "mux_c_1_1" (var hashes_15)
  @@ elet "mux_s" (var pathIndices_15)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_16 (var "poseidons_out")
  @@ elet "var_1_17" (F.const 0)
  @@ assert_eq_in "_assertion_17"
       F.(var pathIndices_16 * F.(F.const 1 - var pathIndices_16))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_16)
  @@ elet "mux_c_0_1" (var siblings_16)
  @@ elet "mux_c_1_0" (var siblings_16)
  @@ elet "mux_c_1_1" (var hashes_16)
  @@ elet "mux_s" (var pathIndices_16)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_17 (var "poseidons_out")
  @@ elet "var_1_18" (F.const 0)
  @@ assert_eq_in "_assertion_18"
       F.(var pathIndices_17 * F.(F.const 1 - var pathIndices_17))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_17)
  @@ elet "mux_c_0_1" (var siblings_17)
  @@ elet "mux_c_1_0" (var siblings_17)
  @@ elet "mux_c_1_1" (var hashes_17)
  @@ elet "mux_s" (var pathIndices_17)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_18 (var "poseidons_out")
  @@ elet "var_1_19" (F.const 0)
  @@ assert_eq_in "_assertion_19"
       F.(var pathIndices_18 * F.(F.const 1 - var pathIndices_18))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_18)
  @@ elet "mux_c_0_1" (var siblings_18)
  @@ elet "mux_c_1_0" (var siblings_18)
  @@ elet "mux_c_1_1" (var hashes_18)
  @@ elet "mux_s" (var pathIndices_18)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_19 (var "poseidons_out")
  @@ elet "var_1_20" (F.const 0)
  @@ assert_eq_in "_assertion_20"
       F.(var pathIndices_19 * F.(F.const 1 - var pathIndices_19))
       (F.const 0)
  @@ elet "mux_c_0_0" (var hashes_19)
  @@ elet "mux_c_0_1" (var siblings_19)
  @@ elet "mux_c_1_0" (var siblings_19)
  @@ elet "mux_c_1_1" (var hashes_19)
  @@ elet "mux_s" (var pathIndices_19)
  @@ body_MultiMux1
       ( "mux_out_0"
       , "mux_out_1"
       , "mux_c_0_0"
       , "mux_c_0_1"
       , "mux_c_1_0"
       , "mux_c_1_1"
       , "mux_s" )
  @@ elet "poseidons_inputs_0" (var "mux_out_0")
  @@ elet "poseidons_inputs_1" (var "mux_out_1")
  @@ body_Poseidon ("poseidons_out", "poseidons_inputs_0", "poseidons_inputs_1")
  @@ elet hashes_20 (var "poseidons_out")
  @@ elet "var_1_21" (F.const 0)
  @@ elet root (var hashes_20)
  @@ body

let circuit_MerkleTreeInclusionProof =
  Circuit
    { name= "MerkleTreeInclusionProof"
    ; inputs=
        [ ("leaf", field)
        ; ("pathIndices_0", field)
        ; ("pathIndices_1", field)
        ; ("pathIndices_2", field)
        ; ("pathIndices_3", field)
        ; ("pathIndices_4", field)
        ; ("pathIndices_5", field)
        ; ("pathIndices_6", field)
        ; ("pathIndices_7", field)
        ; ("pathIndices_8", field)
        ; ("pathIndices_9", field)
        ; ("pathIndices_10", field)
        ; ("pathIndices_11", field)
        ; ("pathIndices_12", field)
        ; ("pathIndices_13", field)
        ; ("pathIndices_14", field)
        ; ("pathIndices_15", field)
        ; ("pathIndices_16", field)
        ; ("pathIndices_17", field)
        ; ("pathIndices_18", field)
        ; ("pathIndices_19", field)
        ; ("siblings_0", field)
        ; ("siblings_1", field)
        ; ("siblings_2", field)
        ; ("siblings_3", field)
        ; ("siblings_4", field)
        ; ("siblings_5", field)
        ; ("siblings_6", field)
        ; ("siblings_7", field)
        ; ("siblings_8", field)
        ; ("siblings_9", field)
        ; ("siblings_10", field)
        ; ("siblings_11", field)
        ; ("siblings_12", field)
        ; ("siblings_13", field)
        ; ("siblings_14", field)
        ; ("siblings_15", field)
        ; ("siblings_16", field)
        ; ("siblings_17", field)
        ; ("siblings_18", field)
        ; ("siblings_19", field) ]
    ; outputs= [("root", field)]
    ; dep= None
    ; body=
        body_MerkleTreeInclusionProof
          ( "root"
          , "leaf"
          , "pathIndices_0"
          , "pathIndices_1"
          , "pathIndices_2"
          , "pathIndices_3"
          , "pathIndices_4"
          , "pathIndices_5"
          , "pathIndices_6"
          , "pathIndices_7"
          , "pathIndices_8"
          , "pathIndices_9"
          , "pathIndices_10"
          , "pathIndices_11"
          , "pathIndices_12"
          , "pathIndices_13"
          , "pathIndices_14"
          , "pathIndices_15"
          , "pathIndices_16"
          , "pathIndices_17"
          , "pathIndices_18"
          , "pathIndices_19"
          , "siblings_0"
          , "siblings_1"
          , "siblings_2"
          , "siblings_3"
          , "siblings_4"
          , "siblings_5"
          , "siblings_6"
          , "siblings_7"
          , "siblings_8"
          , "siblings_9"
          , "siblings_10"
          , "siblings_11"
          , "siblings_12"
          , "siblings_13"
          , "siblings_14"
          , "siblings_15"
          , "siblings_16"
          , "siblings_17"
          , "siblings_18"
          , "siblings_19"
          , "hashes_0"
          , "hashes_1"
          , "hashes_2"
          , "hashes_3"
          , "hashes_4"
          , "hashes_5"
          , "hashes_6"
          , "hashes_7"
          , "hashes_8"
          , "hashes_9"
          , "hashes_10"
          , "hashes_11"
          , "hashes_12"
          , "hashes_13"
          , "hashes_14"
          , "hashes_15"
          , "hashes_16"
          , "hashes_17"
          , "hashes_18"
          , "hashes_19"
          , "hashes_20" )
          (Expr.tuple [var "root"]) }

let body_Semaphore
    ( root
    , nullifierHash
    , signalHash
    , externalNullifier
    , identityNullifier
    , identityTrapdoor
    , treePathIndices_0
    , treePathIndices_1
    , treePathIndices_2
    , treePathIndices_3
    , treePathIndices_4
    , treePathIndices_5
    , treePathIndices_6
    , treePathIndices_7
    , treePathIndices_8
    , treePathIndices_9
    , treePathIndices_10
    , treePathIndices_11
    , treePathIndices_12
    , treePathIndices_13
    , treePathIndices_14
    , treePathIndices_15
    , treePathIndices_16
    , treePathIndices_17
    , treePathIndices_18
    , treePathIndices_19
    , treeSiblings_0
    , treeSiblings_1
    , treeSiblings_2
    , treeSiblings_3
    , treeSiblings_4
    , treeSiblings_5
    , treeSiblings_6
    , treeSiblings_7
    , treeSiblings_8
    , treeSiblings_9
    , treeSiblings_10
    , treeSiblings_11
    , treeSiblings_12
    , treeSiblings_13
    , treeSiblings_14
    , treeSiblings_15
    , treeSiblings_16
    , treeSiblings_17
    , treeSiblings_18
    , treeSiblings_19
    , secret
    , signalHashSquared ) body =
  elet "var_0_1" (F.const 20)
  @@ elet "calculateSecret_identityNullifier" (var identityNullifier)
  @@ elet "calculateSecret_identityTrapdoor" (var identityTrapdoor)
  @@ body_CalculateSecret
       ( "calculateSecret_out"
       , "calculateSecret_identityNullifier"
       , "calculateSecret_identityTrapdoor" )
  @@ elet secret (var "calculateSecret_out")
  @@ elet "calculateIdentityCommitment_secret" (var secret)
  @@ body_CalculateIdentityCommitment
       ("calculateIdentityCommitment_out", "calculateIdentityCommitment_secret")
  @@ elet "calculateNullifierHash_externalNullifier" (var externalNullifier)
  @@ elet "calculateNullifierHash_identityNullifier" (var identityNullifier)
  @@ body_CalculateNullifierHash
       ( "calculateNullifierHash_out"
       , "calculateNullifierHash_externalNullifier"
       , "calculateNullifierHash_identityNullifier" )
  @@ elet "inclusionProof_leaf" (var "calculateIdentityCommitment_out")
  @@ elet "var_1_1" (F.const 0)
  @@ elet "inclusionProof_siblings_0" (var treeSiblings_0)
  @@ elet "inclusionProof_pathIndices_0" (var treePathIndices_0)
  @@ elet "var_1_2" (F.const 0)
  @@ elet "inclusionProof_siblings_1" (var treeSiblings_1)
  @@ elet "inclusionProof_pathIndices_1" (var treePathIndices_1)
  @@ elet "var_1_3" (F.const 0)
  @@ elet "inclusionProof_siblings_2" (var treeSiblings_2)
  @@ elet "inclusionProof_pathIndices_2" (var treePathIndices_2)
  @@ elet "var_1_4" (F.const 0)
  @@ elet "inclusionProof_siblings_3" (var treeSiblings_3)
  @@ elet "inclusionProof_pathIndices_3" (var treePathIndices_3)
  @@ elet "var_1_5" (F.const 0)
  @@ elet "inclusionProof_siblings_4" (var treeSiblings_4)
  @@ elet "inclusionProof_pathIndices_4" (var treePathIndices_4)
  @@ elet "var_1_6" (F.const 0)
  @@ elet "inclusionProof_siblings_5" (var treeSiblings_5)
  @@ elet "inclusionProof_pathIndices_5" (var treePathIndices_5)
  @@ elet "var_1_7" (F.const 0)
  @@ elet "inclusionProof_siblings_6" (var treeSiblings_6)
  @@ elet "inclusionProof_pathIndices_6" (var treePathIndices_6)
  @@ elet "var_1_8" (F.const 0)
  @@ elet "inclusionProof_siblings_7" (var treeSiblings_7)
  @@ elet "inclusionProof_pathIndices_7" (var treePathIndices_7)
  @@ elet "var_1_9" (F.const 0)
  @@ elet "inclusionProof_siblings_8" (var treeSiblings_8)
  @@ elet "inclusionProof_pathIndices_8" (var treePathIndices_8)
  @@ elet "var_1_10" (F.const 0)
  @@ elet "inclusionProof_siblings_9" (var treeSiblings_9)
  @@ elet "inclusionProof_pathIndices_9" (var treePathIndices_9)
  @@ elet "var_1_11" (F.const 0)
  @@ elet "inclusionProof_siblings_10" (var treeSiblings_10)
  @@ elet "inclusionProof_pathIndices_10" (var treePathIndices_10)
  @@ elet "var_1_12" (F.const 0)
  @@ elet "inclusionProof_siblings_11" (var treeSiblings_11)
  @@ elet "inclusionProof_pathIndices_11" (var treePathIndices_11)
  @@ elet "var_1_13" (F.const 0)
  @@ elet "inclusionProof_siblings_12" (var treeSiblings_12)
  @@ elet "inclusionProof_pathIndices_12" (var treePathIndices_12)
  @@ elet "var_1_14" (F.const 0)
  @@ elet "inclusionProof_siblings_13" (var treeSiblings_13)
  @@ elet "inclusionProof_pathIndices_13" (var treePathIndices_13)
  @@ elet "var_1_15" (F.const 0)
  @@ elet "inclusionProof_siblings_14" (var treeSiblings_14)
  @@ elet "inclusionProof_pathIndices_14" (var treePathIndices_14)
  @@ elet "var_1_16" (F.const 0)
  @@ elet "inclusionProof_siblings_15" (var treeSiblings_15)
  @@ elet "inclusionProof_pathIndices_15" (var treePathIndices_15)
  @@ elet "var_1_17" (F.const 0)
  @@ elet "inclusionProof_siblings_16" (var treeSiblings_16)
  @@ elet "inclusionProof_pathIndices_16" (var treePathIndices_16)
  @@ elet "var_1_18" (F.const 0)
  @@ elet "inclusionProof_siblings_17" (var treeSiblings_17)
  @@ elet "inclusionProof_pathIndices_17" (var treePathIndices_17)
  @@ elet "var_1_19" (F.const 0)
  @@ elet "inclusionProof_siblings_18" (var treeSiblings_18)
  @@ elet "inclusionProof_pathIndices_18" (var treePathIndices_18)
  @@ elet "var_1_20" (F.const 0)
  @@ elet "inclusionProof_siblings_19" (var treeSiblings_19)
  @@ elet "inclusionProof_pathIndices_19" (var treePathIndices_19)
  @@ body_MerkleTreeInclusionProof
       ( "inclusionProof_root"
       , "inclusionProof_leaf"
       , "inclusionProof_pathIndices_0"
       , "inclusionProof_pathIndices_1"
       , "inclusionProof_pathIndices_2"
       , "inclusionProof_pathIndices_3"
       , "inclusionProof_pathIndices_4"
       , "inclusionProof_pathIndices_5"
       , "inclusionProof_pathIndices_6"
       , "inclusionProof_pathIndices_7"
       , "inclusionProof_pathIndices_8"
       , "inclusionProof_pathIndices_9"
       , "inclusionProof_pathIndices_10"
       , "inclusionProof_pathIndices_11"
       , "inclusionProof_pathIndices_12"
       , "inclusionProof_pathIndices_13"
       , "inclusionProof_pathIndices_14"
       , "inclusionProof_pathIndices_15"
       , "inclusionProof_pathIndices_16"
       , "inclusionProof_pathIndices_17"
       , "inclusionProof_pathIndices_18"
       , "inclusionProof_pathIndices_19"
       , "inclusionProof_siblings_0"
       , "inclusionProof_siblings_1"
       , "inclusionProof_siblings_2"
       , "inclusionProof_siblings_3"
       , "inclusionProof_siblings_4"
       , "inclusionProof_siblings_5"
       , "inclusionProof_siblings_6"
       , "inclusionProof_siblings_7"
       , "inclusionProof_siblings_8"
       , "inclusionProof_siblings_9"
       , "inclusionProof_siblings_10"
       , "inclusionProof_siblings_11"
       , "inclusionProof_siblings_12"
       , "inclusionProof_siblings_13"
       , "inclusionProof_siblings_14"
       , "inclusionProof_siblings_15"
       , "inclusionProof_siblings_16"
       , "inclusionProof_siblings_17"
       , "inclusionProof_siblings_18"
       , "inclusionProof_siblings_19"
       , "inclusionProof_hashes_0"
       , "inclusionProof_hashes_1"
       , "inclusionProof_hashes_2"
       , "inclusionProof_hashes_3"
       , "inclusionProof_hashes_4"
       , "inclusionProof_hashes_5"
       , "inclusionProof_hashes_6"
       , "inclusionProof_hashes_7"
       , "inclusionProof_hashes_8"
       , "inclusionProof_hashes_9"
       , "inclusionProof_hashes_10"
       , "inclusionProof_hashes_11"
       , "inclusionProof_hashes_12"
       , "inclusionProof_hashes_13"
       , "inclusionProof_hashes_14"
       , "inclusionProof_hashes_15"
       , "inclusionProof_hashes_16"
       , "inclusionProof_hashes_17"
       , "inclusionProof_hashes_18"
       , "inclusionProof_hashes_19"
       , "inclusionProof_hashes_20" )
  @@ elet "var_1_21" (F.const 0)
  @@ elet root (var "inclusionProof_root")
  @@ elet signalHashSquared F.(var signalHash * var signalHash)
  @@ elet nullifierHash (var "calculateNullifierHash_out")
  @@ body

let circuit_Semaphore =
  Circuit
    { name= "Semaphore"
    ; inputs=
        [ ("signalHash", field)
        ; ("externalNullifier", field)
        ; ("identityNullifier", field)
        ; ("identityTrapdoor", field)
        ; ("treePathIndices_0", field)
        ; ("treePathIndices_1", field)
        ; ("treePathIndices_2", field)
        ; ("treePathIndices_3", field)
        ; ("treePathIndices_4", field)
        ; ("treePathIndices_5", field)
        ; ("treePathIndices_6", field)
        ; ("treePathIndices_7", field)
        ; ("treePathIndices_8", field)
        ; ("treePathIndices_9", field)
        ; ("treePathIndices_10", field)
        ; ("treePathIndices_11", field)
        ; ("treePathIndices_12", field)
        ; ("treePathIndices_13", field)
        ; ("treePathIndices_14", field)
        ; ("treePathIndices_15", field)
        ; ("treePathIndices_16", field)
        ; ("treePathIndices_17", field)
        ; ("treePathIndices_18", field)
        ; ("treePathIndices_19", field)
        ; ("treeSiblings_0", field)
        ; ("treeSiblings_1", field)
        ; ("treeSiblings_2", field)
        ; ("treeSiblings_3", field)
        ; ("treeSiblings_4", field)
        ; ("treeSiblings_5", field)
        ; ("treeSiblings_6", field)
        ; ("treeSiblings_7", field)
        ; ("treeSiblings_8", field)
        ; ("treeSiblings_9", field)
        ; ("treeSiblings_10", field)
        ; ("treeSiblings_11", field)
        ; ("treeSiblings_12", field)
        ; ("treeSiblings_13", field)
        ; ("treeSiblings_14", field)
        ; ("treeSiblings_15", field)
        ; ("treeSiblings_16", field)
        ; ("treeSiblings_17", field)
        ; ("treeSiblings_18", field)
        ; ("treeSiblings_19", field) ]
    ; outputs=
        [ ( "root"
          , t_semaphore_root
              ( const_array field
              @@ List.map var
                   [ "treePathIndices_0"
                   ; "treePathIndices_1"
                   ; "treePathIndices_2"
                   ; "treePathIndices_3"
                   ; "treePathIndices_4"
                   ; "treePathIndices_5"
                   ; "treePathIndices_6"
                   ; "treePathIndices_7"
                   ; "treePathIndices_8"
                   ; "treePathIndices_9"
                   ; "treePathIndices_10"
                   ; "treePathIndices_11"
                   ; "treePathIndices_12"
                   ; "treePathIndices_13"
                   ; "treePathIndices_14"
                   ; "treePathIndices_15"
                   ; "treePathIndices_16"
                   ; "treePathIndices_17"
                   ; "treePathIndices_18"
                   ; "treePathIndices_19" ] )
              ( const_array field
              @@ List.map var
                   [ "treeSiblings_0"
                   ; "treeSiblings_1"
                   ; "treeSiblings_2"
                   ; "treeSiblings_3"
                   ; "treeSiblings_4"
                   ; "treeSiblings_5"
                   ; "treeSiblings_6"
                   ; "treeSiblings_7"
                   ; "treeSiblings_8"
                   ; "treeSiblings_9"
                   ; "treeSiblings_10"
                   ; "treeSiblings_11"
                   ; "treeSiblings_12"
                   ; "treeSiblings_13"
                   ; "treeSiblings_14"
                   ; "treeSiblings_15"
                   ; "treeSiblings_16"
                   ; "treeSiblings_17"
                   ; "treeSiblings_18"
                   ; "treeSiblings_19" ] ) )
        ; ("nullifierHash", t_semaphore_null_hash) ]
    ; dep= None
    ; body=
        body_Semaphore
          ( "root"
          , "nullifierHash"
          , "signalHash"
          , "externalNullifier"
          , "identityNullifier"
          , "identityTrapdoor"
          , "treePathIndices_0"
          , "treePathIndices_1"
          , "treePathIndices_2"
          , "treePathIndices_3"
          , "treePathIndices_4"
          , "treePathIndices_5"
          , "treePathIndices_6"
          , "treePathIndices_7"
          , "treePathIndices_8"
          , "treePathIndices_9"
          , "treePathIndices_10"
          , "treePathIndices_11"
          , "treePathIndices_12"
          , "treePathIndices_13"
          , "treePathIndices_14"
          , "treePathIndices_15"
          , "treePathIndices_16"
          , "treePathIndices_17"
          , "treePathIndices_18"
          , "treePathIndices_19"
          , "treeSiblings_0"
          , "treeSiblings_1"
          , "treeSiblings_2"
          , "treeSiblings_3"
          , "treeSiblings_4"
          , "treeSiblings_5"
          , "treeSiblings_6"
          , "treeSiblings_7"
          , "treeSiblings_8"
          , "treeSiblings_9"
          , "treeSiblings_10"
          , "treeSiblings_11"
          , "treeSiblings_12"
          , "treeSiblings_13"
          , "treeSiblings_14"
          , "treeSiblings_15"
          , "treeSiblings_16"
          , "treeSiblings_17"
          , "treeSiblings_18"
          , "treeSiblings_19"
          , "secret"
          , "signalHashSquared" )
          (Expr.tuple [var "root"; var "nullifierHash"]) }
