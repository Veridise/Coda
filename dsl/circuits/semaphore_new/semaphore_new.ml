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

let circuit_Ark =
  Circuit
    { name= "Ark"
    ; inputs= [("in_0", field); ("in_1", field); ("in_2", field)]
    ; outputs= [("out_0", field); ("out_1", field); ("out_2", field)]
    ; dep= None
    ; body=
        body_Ark
          ("out_0", "out_1", "out_2", "in_0", "in_1", "in_2")
          (Expr.tuple [var "out_0"; var "out_1"; var "out_2"]) }

let body_Sigma (out, in_, in2, in4) body =
  elet out star @@ elet in_ star @@ elet in2 star @@ elet in4 star @@ body

let circuit_Sigma =
  Circuit
    { name= "Sigma"
    ; inputs= [("in_", field)]
    ; outputs= [("out", field)]
    ; dep= None
    ; body= body_Sigma ("out", "in_", "in2", "in4") (Expr.tuple [var "out"]) }

let body_Mix (out_0, out_1, out_2, in_0, in_1, in_2) body =
  elet out_0 star @@ elet out_1 star @@ elet out_2 star @@ elet in_0 star
  @@ elet in_1 star @@ elet in_2 star @@ body

let circuit_Mix =
  Circuit
    { name= "Mix"
    ; inputs= [("in_0", field); ("in_1", field); ("in_2", field)]
    ; outputs= [("out_0", field); ("out_1", field); ("out_2", field)]
    ; dep= None
    ; body=
        body_Mix
          ("out_0", "out_1", "out_2", "in_0", "in_1", "in_2")
          (Expr.tuple [var "out_0"; var "out_1"; var "out_2"]) }

let body_MixS (out_0, out_1, out_2, in_0, in_1, in_2) body =
  elet out_0 star @@ elet out_1 star @@ elet out_2 star @@ elet in_0 star
  @@ elet in_1 star @@ elet in_2 star @@ body

let circuit_MixS =
  Circuit
    { name= "MixS"
    ; inputs= [("in_0", field); ("in_1", field); ("in_2", field)]
    ; outputs= [("out_0", field); ("out_1", field); ("out_2", field)]
    ; dep= None
    ; body=
        body_MixS
          ("out_0", "out_1", "out_2", "in_0", "in_1", "in_2")
          (Expr.tuple [var "out_0"; var "out_1"; var "out_2"]) }

let body_MixLast (out, in_0, in_1, in_2) body =
  elet out star @@ elet in_0 star @@ elet in_1 star @@ elet in_2 star @@ body

let circuit_MixLast =
  Circuit
    { name= "MixLast"
    ; inputs= [("in_0", field); ("in_1", field); ("in_2", field)]
    ; outputs= [("out", field)]
    ; dep= None
    ; body=
        body_MixLast ("out", "in_0", "in_1", "in_2") (Expr.tuple [var "out"]) }

let body_PoseidonEx (out_0, inputs_0, inputs_1, initialState) body =
  elet out_0 star @@ elet inputs_0 star @@ elet inputs_1 star
  @@ elet initialState star @@ body

let circuit_PoseidonEx =
  Circuit
    { name= "PoseidonEx"
    ; inputs= [("inputs_0", field); ("inputs_1", field); ("initialState", field)]
    ; outputs= [("out_0", field)]
    ; dep= None
    ; body=
        body_PoseidonEx
          ("out_0", "inputs_0", "inputs_1", "initialState")
          (Expr.tuple [var "out_0"]) }

let body_Poseidon (out, inputs_0, inputs_1) body =
  elet out star @@ elet inputs_0 star @@ elet inputs_1 star @@ body

let circuit_Poseidon =
  Circuit
    { name= "Poseidon"
    ; inputs= [("inputs_0", field); ("inputs_1", field)]
    ; outputs= [("out", field)]
    ; dep= None
    ; body=
        body_Poseidon ("out", "inputs_0", "inputs_1") (Expr.tuple [var "out"])
    }

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
  elet "n" (Z.const 2)
  @@ elet "i" (Z.const 0)
  @@ elet out_0 F.(F.(F.(var c_0_1 - var c_0_0) * var s) + var c_0_0)
  @@ elet "i" (Z.const 1)
  @@ elet out_1 F.(F.(F.(var c_1_1 - var c_1_0) * var s) + var c_1_0)
  @@ elet "i" (Z.const 2)
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
  elet root star @@ elet leaf star @@ elet pathIndices_0 star
  @@ elet pathIndices_1 star @@ elet pathIndices_2 star
  @@ elet pathIndices_3 star @@ elet pathIndices_4 star
  @@ elet pathIndices_5 star @@ elet pathIndices_6 star
  @@ elet pathIndices_7 star @@ elet pathIndices_8 star
  @@ elet pathIndices_9 star @@ elet pathIndices_10 star
  @@ elet pathIndices_11 star @@ elet pathIndices_12 star
  @@ elet pathIndices_13 star @@ elet pathIndices_14 star
  @@ elet pathIndices_15 star @@ elet pathIndices_16 star
  @@ elet pathIndices_17 star @@ elet pathIndices_18 star
  @@ elet pathIndices_19 star @@ elet siblings_0 star @@ elet siblings_1 star
  @@ elet siblings_2 star @@ elet siblings_3 star @@ elet siblings_4 star
  @@ elet siblings_5 star @@ elet siblings_6 star @@ elet siblings_7 star
  @@ elet siblings_8 star @@ elet siblings_9 star @@ elet siblings_10 star
  @@ elet siblings_11 star @@ elet siblings_12 star @@ elet siblings_13 star
  @@ elet siblings_14 star @@ elet siblings_15 star @@ elet siblings_16 star
  @@ elet siblings_17 star @@ elet siblings_18 star @@ elet siblings_19 star
  @@ elet hashes_0 star @@ elet hashes_1 star @@ elet hashes_2 star
  @@ elet hashes_3 star @@ elet hashes_4 star @@ elet hashes_5 star
  @@ elet hashes_6 star @@ elet hashes_7 star @@ elet hashes_8 star
  @@ elet hashes_9 star @@ elet hashes_10 star @@ elet hashes_11 star
  @@ elet hashes_12 star @@ elet hashes_13 star @@ elet hashes_14 star
  @@ elet hashes_15 star @@ elet hashes_16 star @@ elet hashes_17 star
  @@ elet hashes_18 star @@ elet hashes_19 star @@ elet hashes_20 star @@ body

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
  elet "nLevels" (Z.const 20)
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
  @@ elet "i" (Z.const 0)
  @@ elet "inclusionProof_siblings_0" (var treeSiblings_0)
  @@ elet "inclusionProof_pathIndices_0" (var treePathIndices_0)
  @@ elet "i" (Z.const 1)
  @@ elet "inclusionProof_siblings_1" (var treeSiblings_1)
  @@ elet "inclusionProof_pathIndices_1" (var treePathIndices_1)
  @@ elet "i" (Z.const 2)
  @@ elet "inclusionProof_siblings_2" (var treeSiblings_2)
  @@ elet "inclusionProof_pathIndices_2" (var treePathIndices_2)
  @@ elet "i" (Z.const 3)
  @@ elet "inclusionProof_siblings_3" (var treeSiblings_3)
  @@ elet "inclusionProof_pathIndices_3" (var treePathIndices_3)
  @@ elet "i" (Z.const 4)
  @@ elet "inclusionProof_siblings_4" (var treeSiblings_4)
  @@ elet "inclusionProof_pathIndices_4" (var treePathIndices_4)
  @@ elet "i" (Z.const 5)
  @@ elet "inclusionProof_siblings_5" (var treeSiblings_5)
  @@ elet "inclusionProof_pathIndices_5" (var treePathIndices_5)
  @@ elet "i" (Z.const 6)
  @@ elet "inclusionProof_siblings_6" (var treeSiblings_6)
  @@ elet "inclusionProof_pathIndices_6" (var treePathIndices_6)
  @@ elet "i" (Z.const 7)
  @@ elet "inclusionProof_siblings_7" (var treeSiblings_7)
  @@ elet "inclusionProof_pathIndices_7" (var treePathIndices_7)
  @@ elet "i" (Z.const 8)
  @@ elet "inclusionProof_siblings_8" (var treeSiblings_8)
  @@ elet "inclusionProof_pathIndices_8" (var treePathIndices_8)
  @@ elet "i" (Z.const 9)
  @@ elet "inclusionProof_siblings_9" (var treeSiblings_9)
  @@ elet "inclusionProof_pathIndices_9" (var treePathIndices_9)
  @@ elet "i" (Z.const 10)
  @@ elet "inclusionProof_siblings_10" (var treeSiblings_10)
  @@ elet "inclusionProof_pathIndices_10" (var treePathIndices_10)
  @@ elet "i" (Z.const 11)
  @@ elet "inclusionProof_siblings_11" (var treeSiblings_11)
  @@ elet "inclusionProof_pathIndices_11" (var treePathIndices_11)
  @@ elet "i" (Z.const 12)
  @@ elet "inclusionProof_siblings_12" (var treeSiblings_12)
  @@ elet "inclusionProof_pathIndices_12" (var treePathIndices_12)
  @@ elet "i" (Z.const 13)
  @@ elet "inclusionProof_siblings_13" (var treeSiblings_13)
  @@ elet "inclusionProof_pathIndices_13" (var treePathIndices_13)
  @@ elet "i" (Z.const 14)
  @@ elet "inclusionProof_siblings_14" (var treeSiblings_14)
  @@ elet "inclusionProof_pathIndices_14" (var treePathIndices_14)
  @@ elet "i" (Z.const 15)
  @@ elet "inclusionProof_siblings_15" (var treeSiblings_15)
  @@ elet "inclusionProof_pathIndices_15" (var treePathIndices_15)
  @@ elet "i" (Z.const 16)
  @@ elet "inclusionProof_siblings_16" (var treeSiblings_16)
  @@ elet "inclusionProof_pathIndices_16" (var treePathIndices_16)
  @@ elet "i" (Z.const 17)
  @@ elet "inclusionProof_siblings_17" (var treeSiblings_17)
  @@ elet "inclusionProof_pathIndices_17" (var treePathIndices_17)
  @@ elet "i" (Z.const 18)
  @@ elet "inclusionProof_siblings_18" (var treeSiblings_18)
  @@ elet "inclusionProof_pathIndices_18" (var treePathIndices_18)
  @@ elet "i" (Z.const 19)
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
  @@ elet "i" (Z.const 20)
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
        (* let t_semaphore_root treePathIndices treeSiblings = *)
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
