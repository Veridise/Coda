open Ast
open Dsl
open Nice_dsl
open Expr
open Typ

let nLevels = 20

let expand_array_var (x : string) : expr list =
  List.init nLevels (fun i -> var (x ^ "_i" ^ string_of_int i))

(* -------------------------------------------------------------------------- *)
(* Included from `semaphore.ml` *)
(* -------------------------------------------------------------------------- *)

let secret = var "secret"

let identityNullifier = var "identityNullifier"

let externalNullifier = var "externalNullifier"

let u_calc_null_hash x y = unint "CalculateNullifierHash" [x; y]

(* { F | nu =  #CalculateNullifierHash externalNullifier identityNullifier } *)
let t_semaphore_null_hash_qual =
  qeq nu (u_calc_null_hash externalNullifier identityNullifier)

let identityNullifier = var "identityNullifier"

let identityTrapdoor = var "identityTrapdoor"

let t_semaphore_null_hash = tfq t_semaphore_null_hash_qual

let u_calc_id_commit x = unint "CalculateIdentityCommitment" [x]

let u_calc_secret x y = unint "CalculateSecret" [x; y]

let u_calc_null_hash x y = unint "CalculateNullifierHash" [x; y]

let u_mrkl_tree_incl_pf xs i s = unint "MerkleTreeInclusionProof" [xs; i; s]

let u_zip xs ys = unint "zip" [xs; ys]

let u_hasher z init = unint "MrklTreeInclPfHash" [z; init]

let u_poseidon n xs = unint "Poseidon" [n; xs]

let t_calc_secret =
  tfq
    (qeq nu
       (u_poseidon z2 (const_array tf [identityNullifier; identityTrapdoor])) )

let t_calc_id_commit = tfq (qeq nu (u_poseidon z1 (const_array tf [secret])))

let t_calc_null_hash =
  tfq
    (qeq nu
       (u_poseidon z2 (const_array tf [externalNullifier; identityNullifier])) )

(* {F | nu = #MrklTreeInclPfHash (zip pathIndices siblings) leaf } *)
let t_r =
  let pathIndices = const_array field (expand_array_var "pathIndices") in
  let siblings = const_array field (expand_array_var "siblings") in
  tfq (qeq nu (u_hasher (u_zip pathIndices siblings) (var "leaf")))

(* { F | nu = #MerkleTreeInclusionProof
         (#CalculateIdentityCommitment (#CalculateSecret identityNullifier identityTrapdoor))
         treePathIndices treeSiblings } *)
let t_semaphore_root_qual treePathIndices treeSiblings =
  qeq nu
    (u_mrkl_tree_incl_pf
       (u_calc_id_commit (u_calc_secret identityNullifier identityTrapdoor))
       treePathIndices treeSiblings )

let t_semaphore_root =
  let treePathIndices =
    const_array field (expand_array_var "treePathIndices")
  in
  let treeSiblings = const_array field (expand_array_var "treeSiblings") in
  tfq (t_semaphore_root_qual treePathIndices treeSiblings)

(* Outputs *)

let outputs_CalculateSecret = [("out", t_calc_secret)]

let outputs_CalculateIdentityCommitment = [("out", t_calc_id_commit)]

let outputs_CalculateNullifierHash = [("out", t_calc_null_hash)]

let outputs_MerkleTreeInclusionProof = [("root", t_r)]

let semaphore_outputs =
  [("root", t_semaphore_root); ("nullifierHash", t_semaphore_null_hash)]

(* -------------------------------------------------------------------------- *)
(* Circom->Coda *)
(* -------------------------------------------------------------------------- *)

(* The circuit "Ark" is uninterpreted *)

let circuit_Sigma =
  Circuit
    { name= "Sigma"
    ; inputs= [("in", field)]
    ; outputs= [("out", field)]
    ; dep= None
    ; body=
        elet "in2" F.(var "in" * var "in")
        @@ elet "in4" F.(var "in2" * var "in2")
        @@ elet "out" F.(var "in4" * var "in")
        @@ var "out" }

(* The circuit "Mix" is uninterpreted *)

(* The circuit "MixS" is uninterpreted *)

(* The circuit "MixLast" is uninterpreted *)

(* The circuit "PoseidonEx" is uninterpreted *)

(* The circuit "Poseidon" is uninterpreted *)

let circuit_CalculateSecret =
  Circuit
    { name= "CalculateSecret"
    ; inputs= [("identityNullifier", field); ("identityTrapdoor", field)]
    ; outputs= outputs_CalculateSecret
    ; dep= None
    ; body=
        elet "poseidon_dot_inputs_i0" (var "identityNullifier")
        @@ elet "poseidon_dot_inputs_i1" (var "identityTrapdoor")
        @@ elet "poseidon_result"
             (call "Poseidon"
                [var "poseidon_dot_inputs_i0"; var "poseidon_dot_inputs_i1"] )
        @@ elet "poseidon_dot_out" (var "poseidon_result")
        @@ elet "out" (var "poseidon_dot_out")
        @@ var "out" }

let circuit_CalculateIdentityCommitment =
  Circuit
    { name= "CalculateIdentityCommitment"
    ; inputs= [("secret", field)]
    ; outputs= outputs_CalculateIdentityCommitment
    ; dep= None
    ; body=
        elet "poseidon_dot_inputs_i0" (var "secret")
        @@ elet "poseidon_result"
             (call "Poseidon" [var "poseidon_dot_inputs_i0"])
        @@ elet "poseidon_dot_out" (var "poseidon_result")
        @@ elet "out" (var "poseidon_dot_out")
        @@ var "out" }

let circuit_CalculateNullifierHash =
  Circuit
    { name= "CalculateNullifierHash"
    ; inputs= [("externalNullifier", field); ("identityNullifier", field)]
    ; outputs= outputs_CalculateNullifierHash
    ; dep= None
    ; body=
        elet "poseidon_dot_inputs_i0" (var "externalNullifier")
        @@ elet "poseidon_dot_inputs_i1" (var "identityNullifier")
        @@ elet "poseidon_result"
             (call "Poseidon"
                [var "poseidon_dot_inputs_i0"; var "poseidon_dot_inputs_i1"] )
        @@ elet "poseidon_dot_out" (var "poseidon_result")
        @@ elet "out" (var "poseidon_dot_out")
        @@ var "out" }

(* The circuit "MultiMux1" is uninterpreted *)

let circuit_MerkleTreeInclusionProof =
  Circuit
    { name= "MerkleTreeInclusionProof"
    ; inputs=
        [ ("leaf", field)
        ; ("pathIndices_i0", field)
        ; ("pathIndices_i1", field)
        ; ("pathIndices_i2", field)
        ; ("pathIndices_i3", field)
        ; ("pathIndices_i4", field)
        ; ("pathIndices_i5", field)
        ; ("pathIndices_i6", field)
        ; ("pathIndices_i7", field)
        ; ("pathIndices_i8", field)
        ; ("pathIndices_i9", field)
        ; ("pathIndices_i10", field)
        ; ("pathIndices_i11", field)
        ; ("pathIndices_i12", field)
        ; ("pathIndices_i13", field)
        ; ("pathIndices_i14", field)
        ; ("pathIndices_i15", field)
        ; ("pathIndices_i16", field)
        ; ("pathIndices_i17", field)
        ; ("pathIndices_i18", field)
        ; ("pathIndices_i19", field)
        ; ("siblings_i0", field)
        ; ("siblings_i1", field)
        ; ("siblings_i2", field)
        ; ("siblings_i3", field)
        ; ("siblings_i4", field)
        ; ("siblings_i5", field)
        ; ("siblings_i6", field)
        ; ("siblings_i7", field)
        ; ("siblings_i8", field)
        ; ("siblings_i9", field)
        ; ("siblings_i10", field)
        ; ("siblings_i11", field)
        ; ("siblings_i12", field)
        ; ("siblings_i13", field)
        ; ("siblings_i14", field)
        ; ("siblings_i15", field)
        ; ("siblings_i16", field)
        ; ("siblings_i17", field)
        ; ("siblings_i18", field)
        ; ("siblings_i19", field) ]
    ; outputs= outputs_MerkleTreeInclusionProof
    ; dep= None
    ; body=
        elet "var0_v1" (F.const 20)
        @@ elet "hashes_i0" (var "leaf")
        @@ elet "var1_v1" (F.const 0)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i0" * F.(F.const 1 - var "pathIndices_i0"))
                (F.const 0) )
        @@ elet "mux_dot_c_i0_i0" (var "hashes_i0")
        @@ elet "mux_dot_c_i0_i1" (var "siblings_i0")
        @@ elet "mux_dot_c_i1_i0" (var "siblings_i0")
        @@ elet "mux_dot_c_i1_i1" (var "hashes_i0")
        @@ elet "mux_dot_s" (var "pathIndices_i0")
        @@ elet "mux_result"
             (call "MultiMux1"
                [ var "mux_dot_c_i0_i0"
                ; var "mux_dot_c_i0_i1"
                ; var "mux_dot_c_i1_i0"
                ; var "mux_dot_c_i1_i1"
                ; var "mux_dot_s" ] )
        @@ elet "mux_dot_out_i0" (project (var "mux_result") 1)
        @@ elet "mux_dot_out_i1" (project (var "mux_result") 0)
        @@ elet "poseidons_dot_inputs_i0" (var "mux_dot_out_i0")
        @@ elet "poseidons_dot_inputs_i1" (var "mux_dot_out_i1")
        @@ elet "poseidons_result"
             (call "Poseidon"
                [var "poseidons_dot_inputs_i0"; var "poseidons_dot_inputs_i1"] )
        @@ elet "poseidons_dot_out" (var "poseidons_result")
        @@ elet "hashes_i1" (var "poseidons_dot_out")
        @@ elet "var1_v2" (F.const 666)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i1" * F.(F.const 1 - var "pathIndices_i1"))
                (F.const 0) )
        @@ elet "mux_c1_dot_c_i0_i0" (var "hashes_i1")
        @@ elet "mux_c1_dot_c_i0_i1" (var "siblings_i1")
        @@ elet "mux_c1_dot_c_i1_i0" (var "siblings_i1")
        @@ elet "mux_c1_dot_c_i1_i1" (var "hashes_i1")
        @@ elet "mux_c1_dot_s" (var "pathIndices_i1")
        @@ elet "mux_c1_result"
             (call "MultiMux1"
                [ var "mux_c1_dot_c_i0_i0"
                ; var "mux_c1_dot_c_i0_i1"
                ; var "mux_c1_dot_c_i1_i0"
                ; var "mux_c1_dot_c_i1_i1"
                ; var "mux_c1_dot_s" ] )
        @@ elet "mux_c1_dot_out_i0" (project (var "mux_c1_result") 1)
        @@ elet "mux_c1_dot_out_i1" (project (var "mux_c1_result") 0)
        @@ elet "poseidons_c1_dot_inputs_i0" (var "mux_c1_dot_out_i0")
        @@ elet "poseidons_c1_dot_inputs_i1" (var "mux_c1_dot_out_i1")
        @@ elet "poseidons_c1_result"
             (call "Poseidon"
                [ var "poseidons_c1_dot_inputs_i0"
                ; var "poseidons_c1_dot_inputs_i1" ] )
        @@ elet "poseidons_c1_dot_out" (var "poseidons_c1_result")
        @@ elet "hashes_i2" (var "poseidons_c1_dot_out")
        @@ elet "var1_v3" (F.const 666)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i2" * F.(F.const 1 - var "pathIndices_i2"))
                (F.const 0) )
        @@ elet "mux_c2_dot_c_i0_i0" (var "hashes_i2")
        @@ elet "mux_c2_dot_c_i0_i1" (var "siblings_i2")
        @@ elet "mux_c2_dot_c_i1_i0" (var "siblings_i2")
        @@ elet "mux_c2_dot_c_i1_i1" (var "hashes_i2")
        @@ elet "mux_c2_dot_s" (var "pathIndices_i2")
        @@ elet "mux_c2_result"
             (call "MultiMux1"
                [ var "mux_c2_dot_c_i0_i0"
                ; var "mux_c2_dot_c_i0_i1"
                ; var "mux_c2_dot_c_i1_i0"
                ; var "mux_c2_dot_c_i1_i1"
                ; var "mux_c2_dot_s" ] )
        @@ elet "mux_c2_dot_out_i0" (project (var "mux_c2_result") 1)
        @@ elet "mux_c2_dot_out_i1" (project (var "mux_c2_result") 0)
        @@ elet "poseidons_c2_dot_inputs_i0" (var "mux_c2_dot_out_i0")
        @@ elet "poseidons_c2_dot_inputs_i1" (var "mux_c2_dot_out_i1")
        @@ elet "poseidons_c2_result"
             (call "Poseidon"
                [ var "poseidons_c2_dot_inputs_i0"
                ; var "poseidons_c2_dot_inputs_i1" ] )
        @@ elet "poseidons_c2_dot_out" (var "poseidons_c2_result")
        @@ elet "hashes_i3" (var "poseidons_c2_dot_out")
        @@ elet "var1_v4" (F.const 666)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i3" * F.(F.const 1 - var "pathIndices_i3"))
                (F.const 0) )
        @@ elet "mux_c3_dot_c_i0_i0" (var "hashes_i3")
        @@ elet "mux_c3_dot_c_i0_i1" (var "siblings_i3")
        @@ elet "mux_c3_dot_c_i1_i0" (var "siblings_i3")
        @@ elet "mux_c3_dot_c_i1_i1" (var "hashes_i3")
        @@ elet "mux_c3_dot_s" (var "pathIndices_i3")
        @@ elet "mux_c3_result"
             (call "MultiMux1"
                [ var "mux_c3_dot_c_i0_i0"
                ; var "mux_c3_dot_c_i0_i1"
                ; var "mux_c3_dot_c_i1_i0"
                ; var "mux_c3_dot_c_i1_i1"
                ; var "mux_c3_dot_s" ] )
        @@ elet "mux_c3_dot_out_i0" (project (var "mux_c3_result") 1)
        @@ elet "mux_c3_dot_out_i1" (project (var "mux_c3_result") 0)
        @@ elet "poseidons_c3_dot_inputs_i0" (var "mux_c3_dot_out_i0")
        @@ elet "poseidons_c3_dot_inputs_i1" (var "mux_c3_dot_out_i1")
        @@ elet "poseidons_c3_result"
             (call "Poseidon"
                [ var "poseidons_c3_dot_inputs_i0"
                ; var "poseidons_c3_dot_inputs_i1" ] )
        @@ elet "poseidons_c3_dot_out" (var "poseidons_c3_result")
        @@ elet "hashes_i4" (var "poseidons_c3_dot_out")
        @@ elet "var1_v5" (F.const 666)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i4" * F.(F.const 1 - var "pathIndices_i4"))
                (F.const 0) )
        @@ elet "mux_c4_dot_c_i0_i0" (var "hashes_i4")
        @@ elet "mux_c4_dot_c_i0_i1" (var "siblings_i4")
        @@ elet "mux_c4_dot_c_i1_i0" (var "siblings_i4")
        @@ elet "mux_c4_dot_c_i1_i1" (var "hashes_i4")
        @@ elet "mux_c4_dot_s" (var "pathIndices_i4")
        @@ elet "mux_c4_result"
             (call "MultiMux1"
                [ var "mux_c4_dot_c_i0_i0"
                ; var "mux_c4_dot_c_i0_i1"
                ; var "mux_c4_dot_c_i1_i0"
                ; var "mux_c4_dot_c_i1_i1"
                ; var "mux_c4_dot_s" ] )
        @@ elet "mux_c4_dot_out_i0" (project (var "mux_c4_result") 1)
        @@ elet "mux_c4_dot_out_i1" (project (var "mux_c4_result") 0)
        @@ elet "poseidons_c4_dot_inputs_i0" (var "mux_c4_dot_out_i0")
        @@ elet "poseidons_c4_dot_inputs_i1" (var "mux_c4_dot_out_i1")
        @@ elet "poseidons_c4_result"
             (call "Poseidon"
                [ var "poseidons_c4_dot_inputs_i0"
                ; var "poseidons_c4_dot_inputs_i1" ] )
        @@ elet "poseidons_c4_dot_out" (var "poseidons_c4_result")
        @@ elet "hashes_i5" (var "poseidons_c4_dot_out")
        @@ elet "var1_v6" (F.const 666)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i5" * F.(F.const 1 - var "pathIndices_i5"))
                (F.const 0) )
        @@ elet "mux_c5_dot_c_i0_i0" (var "hashes_i5")
        @@ elet "mux_c5_dot_c_i0_i1" (var "siblings_i5")
        @@ elet "mux_c5_dot_c_i1_i0" (var "siblings_i5")
        @@ elet "mux_c5_dot_c_i1_i1" (var "hashes_i5")
        @@ elet "mux_c5_dot_s" (var "pathIndices_i5")
        @@ elet "mux_c5_result"
             (call "MultiMux1"
                [ var "mux_c5_dot_c_i0_i0"
                ; var "mux_c5_dot_c_i0_i1"
                ; var "mux_c5_dot_c_i1_i0"
                ; var "mux_c5_dot_c_i1_i1"
                ; var "mux_c5_dot_s" ] )
        @@ elet "mux_c5_dot_out_i0" (project (var "mux_c5_result") 1)
        @@ elet "mux_c5_dot_out_i1" (project (var "mux_c5_result") 0)
        @@ elet "poseidons_c5_dot_inputs_i0" (var "mux_c5_dot_out_i0")
        @@ elet "poseidons_c5_dot_inputs_i1" (var "mux_c5_dot_out_i1")
        @@ elet "poseidons_c5_result"
             (call "Poseidon"
                [ var "poseidons_c5_dot_inputs_i0"
                ; var "poseidons_c5_dot_inputs_i1" ] )
        @@ elet "poseidons_c5_dot_out" (var "poseidons_c5_result")
        @@ elet "hashes_i6" (var "poseidons_c5_dot_out")
        @@ elet "var1_v7" (F.const 666)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i6" * F.(F.const 1 - var "pathIndices_i6"))
                (F.const 0) )
        @@ elet "mux_c6_dot_c_i0_i0" (var "hashes_i6")
        @@ elet "mux_c6_dot_c_i0_i1" (var "siblings_i6")
        @@ elet "mux_c6_dot_c_i1_i0" (var "siblings_i6")
        @@ elet "mux_c6_dot_c_i1_i1" (var "hashes_i6")
        @@ elet "mux_c6_dot_s" (var "pathIndices_i6")
        @@ elet "mux_c6_result"
             (call "MultiMux1"
                [ var "mux_c6_dot_c_i0_i0"
                ; var "mux_c6_dot_c_i0_i1"
                ; var "mux_c6_dot_c_i1_i0"
                ; var "mux_c6_dot_c_i1_i1"
                ; var "mux_c6_dot_s" ] )
        @@ elet "mux_c6_dot_out_i0" (project (var "mux_c6_result") 1)
        @@ elet "mux_c6_dot_out_i1" (project (var "mux_c6_result") 0)
        @@ elet "poseidons_c6_dot_inputs_i0" (var "mux_c6_dot_out_i0")
        @@ elet "poseidons_c6_dot_inputs_i1" (var "mux_c6_dot_out_i1")
        @@ elet "poseidons_c6_result"
             (call "Poseidon"
                [ var "poseidons_c6_dot_inputs_i0"
                ; var "poseidons_c6_dot_inputs_i1" ] )
        @@ elet "poseidons_c6_dot_out" (var "poseidons_c6_result")
        @@ elet "hashes_i7" (var "poseidons_c6_dot_out")
        @@ elet "var1_v8" (F.const 666)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i7" * F.(F.const 1 - var "pathIndices_i7"))
                (F.const 0) )
        @@ elet "mux_c7_dot_c_i0_i0" (var "hashes_i7")
        @@ elet "mux_c7_dot_c_i0_i1" (var "siblings_i7")
        @@ elet "mux_c7_dot_c_i1_i0" (var "siblings_i7")
        @@ elet "mux_c7_dot_c_i1_i1" (var "hashes_i7")
        @@ elet "mux_c7_dot_s" (var "pathIndices_i7")
        @@ elet "mux_c7_result"
             (call "MultiMux1"
                [ var "mux_c7_dot_c_i0_i0"
                ; var "mux_c7_dot_c_i0_i1"
                ; var "mux_c7_dot_c_i1_i0"
                ; var "mux_c7_dot_c_i1_i1"
                ; var "mux_c7_dot_s" ] )
        @@ elet "mux_c7_dot_out_i0" (project (var "mux_c7_result") 1)
        @@ elet "mux_c7_dot_out_i1" (project (var "mux_c7_result") 0)
        @@ elet "poseidons_c7_dot_inputs_i0" (var "mux_c7_dot_out_i0")
        @@ elet "poseidons_c7_dot_inputs_i1" (var "mux_c7_dot_out_i1")
        @@ elet "poseidons_c7_result"
             (call "Poseidon"
                [ var "poseidons_c7_dot_inputs_i0"
                ; var "poseidons_c7_dot_inputs_i1" ] )
        @@ elet "poseidons_c7_dot_out" (var "poseidons_c7_result")
        @@ elet "hashes_i8" (var "poseidons_c7_dot_out")
        @@ elet "var1_v9" (F.const 666)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i8" * F.(F.const 1 - var "pathIndices_i8"))
                (F.const 0) )
        @@ elet "mux_c8_dot_c_i0_i0" (var "hashes_i8")
        @@ elet "mux_c8_dot_c_i0_i1" (var "siblings_i8")
        @@ elet "mux_c8_dot_c_i1_i0" (var "siblings_i8")
        @@ elet "mux_c8_dot_c_i1_i1" (var "hashes_i8")
        @@ elet "mux_c8_dot_s" (var "pathIndices_i8")
        @@ elet "mux_c8_result"
             (call "MultiMux1"
                [ var "mux_c8_dot_c_i0_i0"
                ; var "mux_c8_dot_c_i0_i1"
                ; var "mux_c8_dot_c_i1_i0"
                ; var "mux_c8_dot_c_i1_i1"
                ; var "mux_c8_dot_s" ] )
        @@ elet "mux_c8_dot_out_i0" (project (var "mux_c8_result") 1)
        @@ elet "mux_c8_dot_out_i1" (project (var "mux_c8_result") 0)
        @@ elet "poseidons_c8_dot_inputs_i0" (var "mux_c8_dot_out_i0")
        @@ elet "poseidons_c8_dot_inputs_i1" (var "mux_c8_dot_out_i1")
        @@ elet "poseidons_c8_result"
             (call "Poseidon"
                [ var "poseidons_c8_dot_inputs_i0"
                ; var "poseidons_c8_dot_inputs_i1" ] )
        @@ elet "poseidons_c8_dot_out" (var "poseidons_c8_result")
        @@ elet "hashes_i9" (var "poseidons_c8_dot_out")
        @@ elet "var1_v10" (F.const 666)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i9" * F.(F.const 1 - var "pathIndices_i9"))
                (F.const 0) )
        @@ elet "mux_c9_dot_c_i0_i0" (var "hashes_i9")
        @@ elet "mux_c9_dot_c_i0_i1" (var "siblings_i9")
        @@ elet "mux_c9_dot_c_i1_i0" (var "siblings_i9")
        @@ elet "mux_c9_dot_c_i1_i1" (var "hashes_i9")
        @@ elet "mux_c9_dot_s" (var "pathIndices_i9")
        @@ elet "mux_c9_result"
             (call "MultiMux1"
                [ var "mux_c9_dot_c_i0_i0"
                ; var "mux_c9_dot_c_i0_i1"
                ; var "mux_c9_dot_c_i1_i0"
                ; var "mux_c9_dot_c_i1_i1"
                ; var "mux_c9_dot_s" ] )
        @@ elet "mux_c9_dot_out_i0" (project (var "mux_c9_result") 1)
        @@ elet "mux_c9_dot_out_i1" (project (var "mux_c9_result") 0)
        @@ elet "poseidons_c9_dot_inputs_i0" (var "mux_c9_dot_out_i0")
        @@ elet "poseidons_c9_dot_inputs_i1" (var "mux_c9_dot_out_i1")
        @@ elet "poseidons_c9_result"
             (call "Poseidon"
                [ var "poseidons_c9_dot_inputs_i0"
                ; var "poseidons_c9_dot_inputs_i1" ] )
        @@ elet "poseidons_c9_dot_out" (var "poseidons_c9_result")
        @@ elet "hashes_i10" (var "poseidons_c9_dot_out")
        @@ elet "var1_v11" (F.const 666)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i10" * F.(F.const 1 - var "pathIndices_i10"))
                (F.const 0) )
        @@ elet "mux_c10_dot_c_i0_i0" (var "hashes_i10")
        @@ elet "mux_c10_dot_c_i0_i1" (var "siblings_i10")
        @@ elet "mux_c10_dot_c_i1_i0" (var "siblings_i10")
        @@ elet "mux_c10_dot_c_i1_i1" (var "hashes_i10")
        @@ elet "mux_c10_dot_s" (var "pathIndices_i10")
        @@ elet "mux_c10_result"
             (call "MultiMux1"
                [ var "mux_c10_dot_c_i0_i0"
                ; var "mux_c10_dot_c_i0_i1"
                ; var "mux_c10_dot_c_i1_i0"
                ; var "mux_c10_dot_c_i1_i1"
                ; var "mux_c10_dot_s" ] )
        @@ elet "mux_c10_dot_out_i0" (project (var "mux_c10_result") 1)
        @@ elet "mux_c10_dot_out_i1" (project (var "mux_c10_result") 0)
        @@ elet "poseidons_c10_dot_inputs_i0" (var "mux_c10_dot_out_i0")
        @@ elet "poseidons_c10_dot_inputs_i1" (var "mux_c10_dot_out_i1")
        @@ elet "poseidons_c10_result"
             (call "Poseidon"
                [ var "poseidons_c10_dot_inputs_i0"
                ; var "poseidons_c10_dot_inputs_i1" ] )
        @@ elet "poseidons_c10_dot_out" (var "poseidons_c10_result")
        @@ elet "hashes_i11" (var "poseidons_c10_dot_out")
        @@ elet "var1_v12" (F.const 666)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i11" * F.(F.const 1 - var "pathIndices_i11"))
                (F.const 0) )
        @@ elet "mux_c11_dot_c_i0_i0" (var "hashes_i11")
        @@ elet "mux_c11_dot_c_i0_i1" (var "siblings_i11")
        @@ elet "mux_c11_dot_c_i1_i0" (var "siblings_i11")
        @@ elet "mux_c11_dot_c_i1_i1" (var "hashes_i11")
        @@ elet "mux_c11_dot_s" (var "pathIndices_i11")
        @@ elet "mux_c11_result"
             (call "MultiMux1"
                [ var "mux_c11_dot_c_i0_i0"
                ; var "mux_c11_dot_c_i0_i1"
                ; var "mux_c11_dot_c_i1_i0"
                ; var "mux_c11_dot_c_i1_i1"
                ; var "mux_c11_dot_s" ] )
        @@ elet "mux_c11_dot_out_i0" (project (var "mux_c11_result") 1)
        @@ elet "mux_c11_dot_out_i1" (project (var "mux_c11_result") 0)
        @@ elet "poseidons_c11_dot_inputs_i0" (var "mux_c11_dot_out_i0")
        @@ elet "poseidons_c11_dot_inputs_i1" (var "mux_c11_dot_out_i1")
        @@ elet "poseidons_c11_result"
             (call "Poseidon"
                [ var "poseidons_c11_dot_inputs_i0"
                ; var "poseidons_c11_dot_inputs_i1" ] )
        @@ elet "poseidons_c11_dot_out" (var "poseidons_c11_result")
        @@ elet "hashes_i12" (var "poseidons_c11_dot_out")
        @@ elet "var1_v13" (F.const 666)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i12" * F.(F.const 1 - var "pathIndices_i12"))
                (F.const 0) )
        @@ elet "mux_c12_dot_c_i0_i0" (var "hashes_i12")
        @@ elet "mux_c12_dot_c_i0_i1" (var "siblings_i12")
        @@ elet "mux_c12_dot_c_i1_i0" (var "siblings_i12")
        @@ elet "mux_c12_dot_c_i1_i1" (var "hashes_i12")
        @@ elet "mux_c12_dot_s" (var "pathIndices_i12")
        @@ elet "mux_c12_result"
             (call "MultiMux1"
                [ var "mux_c12_dot_c_i0_i0"
                ; var "mux_c12_dot_c_i0_i1"
                ; var "mux_c12_dot_c_i1_i0"
                ; var "mux_c12_dot_c_i1_i1"
                ; var "mux_c12_dot_s" ] )
        @@ elet "mux_c12_dot_out_i0" (project (var "mux_c12_result") 1)
        @@ elet "mux_c12_dot_out_i1" (project (var "mux_c12_result") 0)
        @@ elet "poseidons_c12_dot_inputs_i0" (var "mux_c12_dot_out_i0")
        @@ elet "poseidons_c12_dot_inputs_i1" (var "mux_c12_dot_out_i1")
        @@ elet "poseidons_c12_result"
             (call "Poseidon"
                [ var "poseidons_c12_dot_inputs_i0"
                ; var "poseidons_c12_dot_inputs_i1" ] )
        @@ elet "poseidons_c12_dot_out" (var "poseidons_c12_result")
        @@ elet "hashes_i13" (var "poseidons_c12_dot_out")
        @@ elet "var1_v14" (F.const 666)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i13" * F.(F.const 1 - var "pathIndices_i13"))
                (F.const 0) )
        @@ elet "mux_c13_dot_c_i0_i0" (var "hashes_i13")
        @@ elet "mux_c13_dot_c_i0_i1" (var "siblings_i13")
        @@ elet "mux_c13_dot_c_i1_i0" (var "siblings_i13")
        @@ elet "mux_c13_dot_c_i1_i1" (var "hashes_i13")
        @@ elet "mux_c13_dot_s" (var "pathIndices_i13")
        @@ elet "mux_c13_result"
             (call "MultiMux1"
                [ var "mux_c13_dot_c_i0_i0"
                ; var "mux_c13_dot_c_i0_i1"
                ; var "mux_c13_dot_c_i1_i0"
                ; var "mux_c13_dot_c_i1_i1"
                ; var "mux_c13_dot_s" ] )
        @@ elet "mux_c13_dot_out_i0" (project (var "mux_c13_result") 1)
        @@ elet "mux_c13_dot_out_i1" (project (var "mux_c13_result") 0)
        @@ elet "poseidons_c13_dot_inputs_i0" (var "mux_c13_dot_out_i0")
        @@ elet "poseidons_c13_dot_inputs_i1" (var "mux_c13_dot_out_i1")
        @@ elet "poseidons_c13_result"
             (call "Poseidon"
                [ var "poseidons_c13_dot_inputs_i0"
                ; var "poseidons_c13_dot_inputs_i1" ] )
        @@ elet "poseidons_c13_dot_out" (var "poseidons_c13_result")
        @@ elet "hashes_i14" (var "poseidons_c13_dot_out")
        @@ elet "var1_v15" (F.const 666)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i14" * F.(F.const 1 - var "pathIndices_i14"))
                (F.const 0) )
        @@ elet "mux_c14_dot_c_i0_i0" (var "hashes_i14")
        @@ elet "mux_c14_dot_c_i0_i1" (var "siblings_i14")
        @@ elet "mux_c14_dot_c_i1_i0" (var "siblings_i14")
        @@ elet "mux_c14_dot_c_i1_i1" (var "hashes_i14")
        @@ elet "mux_c14_dot_s" (var "pathIndices_i14")
        @@ elet "mux_c14_result"
             (call "MultiMux1"
                [ var "mux_c14_dot_c_i0_i0"
                ; var "mux_c14_dot_c_i0_i1"
                ; var "mux_c14_dot_c_i1_i0"
                ; var "mux_c14_dot_c_i1_i1"
                ; var "mux_c14_dot_s" ] )
        @@ elet "mux_c14_dot_out_i0" (project (var "mux_c14_result") 1)
        @@ elet "mux_c14_dot_out_i1" (project (var "mux_c14_result") 0)
        @@ elet "poseidons_c14_dot_inputs_i0" (var "mux_c14_dot_out_i0")
        @@ elet "poseidons_c14_dot_inputs_i1" (var "mux_c14_dot_out_i1")
        @@ elet "poseidons_c14_result"
             (call "Poseidon"
                [ var "poseidons_c14_dot_inputs_i0"
                ; var "poseidons_c14_dot_inputs_i1" ] )
        @@ elet "poseidons_c14_dot_out" (var "poseidons_c14_result")
        @@ elet "hashes_i15" (var "poseidons_c14_dot_out")
        @@ elet "var1_v16" (F.const 666)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i15" * F.(F.const 1 - var "pathIndices_i15"))
                (F.const 0) )
        @@ elet "mux_c15_dot_c_i0_i0" (var "hashes_i15")
        @@ elet "mux_c15_dot_c_i0_i1" (var "siblings_i15")
        @@ elet "mux_c15_dot_c_i1_i0" (var "siblings_i15")
        @@ elet "mux_c15_dot_c_i1_i1" (var "hashes_i15")
        @@ elet "mux_c15_dot_s" (var "pathIndices_i15")
        @@ elet "mux_c15_result"
             (call "MultiMux1"
                [ var "mux_c15_dot_c_i0_i0"
                ; var "mux_c15_dot_c_i0_i1"
                ; var "mux_c15_dot_c_i1_i0"
                ; var "mux_c15_dot_c_i1_i1"
                ; var "mux_c15_dot_s" ] )
        @@ elet "mux_c15_dot_out_i0" (project (var "mux_c15_result") 1)
        @@ elet "mux_c15_dot_out_i1" (project (var "mux_c15_result") 0)
        @@ elet "poseidons_c15_dot_inputs_i0" (var "mux_c15_dot_out_i0")
        @@ elet "poseidons_c15_dot_inputs_i1" (var "mux_c15_dot_out_i1")
        @@ elet "poseidons_c15_result"
             (call "Poseidon"
                [ var "poseidons_c15_dot_inputs_i0"
                ; var "poseidons_c15_dot_inputs_i1" ] )
        @@ elet "poseidons_c15_dot_out" (var "poseidons_c15_result")
        @@ elet "hashes_i16" (var "poseidons_c15_dot_out")
        @@ elet "var1_v17" (F.const 666)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i16" * F.(F.const 1 - var "pathIndices_i16"))
                (F.const 0) )
        @@ elet "mux_c16_dot_c_i0_i0" (var "hashes_i16")
        @@ elet "mux_c16_dot_c_i0_i1" (var "siblings_i16")
        @@ elet "mux_c16_dot_c_i1_i0" (var "siblings_i16")
        @@ elet "mux_c16_dot_c_i1_i1" (var "hashes_i16")
        @@ elet "mux_c16_dot_s" (var "pathIndices_i16")
        @@ elet "mux_c16_result"
             (call "MultiMux1"
                [ var "mux_c16_dot_c_i0_i0"
                ; var "mux_c16_dot_c_i0_i1"
                ; var "mux_c16_dot_c_i1_i0"
                ; var "mux_c16_dot_c_i1_i1"
                ; var "mux_c16_dot_s" ] )
        @@ elet "mux_c16_dot_out_i0" (project (var "mux_c16_result") 1)
        @@ elet "mux_c16_dot_out_i1" (project (var "mux_c16_result") 0)
        @@ elet "poseidons_c16_dot_inputs_i0" (var "mux_c16_dot_out_i0")
        @@ elet "poseidons_c16_dot_inputs_i1" (var "mux_c16_dot_out_i1")
        @@ elet "poseidons_c16_result"
             (call "Poseidon"
                [ var "poseidons_c16_dot_inputs_i0"
                ; var "poseidons_c16_dot_inputs_i1" ] )
        @@ elet "poseidons_c16_dot_out" (var "poseidons_c16_result")
        @@ elet "hashes_i17" (var "poseidons_c16_dot_out")
        @@ elet "var1_v18" (F.const 666)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i17" * F.(F.const 1 - var "pathIndices_i17"))
                (F.const 0) )
        @@ elet "mux_c17_dot_c_i0_i0" (var "hashes_i17")
        @@ elet "mux_c17_dot_c_i0_i1" (var "siblings_i17")
        @@ elet "mux_c17_dot_c_i1_i0" (var "siblings_i17")
        @@ elet "mux_c17_dot_c_i1_i1" (var "hashes_i17")
        @@ elet "mux_c17_dot_s" (var "pathIndices_i17")
        @@ elet "mux_c17_result"
             (call "MultiMux1"
                [ var "mux_c17_dot_c_i0_i0"
                ; var "mux_c17_dot_c_i0_i1"
                ; var "mux_c17_dot_c_i1_i0"
                ; var "mux_c17_dot_c_i1_i1"
                ; var "mux_c17_dot_s" ] )
        @@ elet "mux_c17_dot_out_i0" (project (var "mux_c17_result") 1)
        @@ elet "mux_c17_dot_out_i1" (project (var "mux_c17_result") 0)
        @@ elet "poseidons_c17_dot_inputs_i0" (var "mux_c17_dot_out_i0")
        @@ elet "poseidons_c17_dot_inputs_i1" (var "mux_c17_dot_out_i1")
        @@ elet "poseidons_c17_result"
             (call "Poseidon"
                [ var "poseidons_c17_dot_inputs_i0"
                ; var "poseidons_c17_dot_inputs_i1" ] )
        @@ elet "poseidons_c17_dot_out" (var "poseidons_c17_result")
        @@ elet "hashes_i18" (var "poseidons_c17_dot_out")
        @@ elet "var1_v19" (F.const 666)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i18" * F.(F.const 1 - var "pathIndices_i18"))
                (F.const 0) )
        @@ elet "mux_c18_dot_c_i0_i0" (var "hashes_i18")
        @@ elet "mux_c18_dot_c_i0_i1" (var "siblings_i18")
        @@ elet "mux_c18_dot_c_i1_i0" (var "siblings_i18")
        @@ elet "mux_c18_dot_c_i1_i1" (var "hashes_i18")
        @@ elet "mux_c18_dot_s" (var "pathIndices_i18")
        @@ elet "mux_c18_result"
             (call "MultiMux1"
                [ var "mux_c18_dot_c_i0_i0"
                ; var "mux_c18_dot_c_i0_i1"
                ; var "mux_c18_dot_c_i1_i0"
                ; var "mux_c18_dot_c_i1_i1"
                ; var "mux_c18_dot_s" ] )
        @@ elet "mux_c18_dot_out_i0" (project (var "mux_c18_result") 1)
        @@ elet "mux_c18_dot_out_i1" (project (var "mux_c18_result") 0)
        @@ elet "poseidons_c18_dot_inputs_i0" (var "mux_c18_dot_out_i0")
        @@ elet "poseidons_c18_dot_inputs_i1" (var "mux_c18_dot_out_i1")
        @@ elet "poseidons_c18_result"
             (call "Poseidon"
                [ var "poseidons_c18_dot_inputs_i0"
                ; var "poseidons_c18_dot_inputs_i1" ] )
        @@ elet "poseidons_c18_dot_out" (var "poseidons_c18_result")
        @@ elet "hashes_i19" (var "poseidons_c18_dot_out")
        @@ elet "var1_v20" (F.const 666)
        @@ elet "fresh_0"
             (assert_eq
                F.(var "pathIndices_i19" * F.(F.const 1 - var "pathIndices_i19"))
                (F.const 0) )
        @@ elet "mux_c19_dot_c_i0_i0" (var "hashes_i19")
        @@ elet "mux_c19_dot_c_i0_i1" (var "siblings_i19")
        @@ elet "mux_c19_dot_c_i1_i0" (var "siblings_i19")
        @@ elet "mux_c19_dot_c_i1_i1" (var "hashes_i19")
        @@ elet "mux_c19_dot_s" (var "pathIndices_i19")
        @@ elet "mux_c19_result"
             (call "MultiMux1"
                [ var "mux_c19_dot_c_i0_i0"
                ; var "mux_c19_dot_c_i0_i1"
                ; var "mux_c19_dot_c_i1_i0"
                ; var "mux_c19_dot_c_i1_i1"
                ; var "mux_c19_dot_s" ] )
        @@ elet "mux_c19_dot_out_i0" (project (var "mux_c19_result") 1)
        @@ elet "mux_c19_dot_out_i1" (project (var "mux_c19_result") 0)
        @@ elet "poseidons_c19_dot_inputs_i0" (var "mux_c19_dot_out_i0")
        @@ elet "poseidons_c19_dot_inputs_i1" (var "mux_c19_dot_out_i1")
        @@ elet "poseidons_c19_result"
             (call "Poseidon"
                [ var "poseidons_c19_dot_inputs_i0"
                ; var "poseidons_c19_dot_inputs_i1" ] )
        @@ elet "poseidons_c19_dot_out" (var "poseidons_c19_result")
        @@ elet "hashes_i20" (var "poseidons_c19_dot_out")
        @@ elet "var1_v21" (F.const 666)
        @@ elet "root" (var "hashes_i20")
        @@ var "root" }

let circuit_Semaphore =
  Circuit
    { name= "Semaphore"
    ; inputs=
        [ ("signalHash", field)
        ; ("externalNullifier", field)
        ; ("identityNullifier", field)
        ; ("identityTrapdoor", field)
        ; ("treePathIndices_i0", field)
        ; ("treePathIndices_i1", field)
        ; ("treePathIndices_i2", field)
        ; ("treePathIndices_i3", field)
        ; ("treePathIndices_i4", field)
        ; ("treePathIndices_i5", field)
        ; ("treePathIndices_i6", field)
        ; ("treePathIndices_i7", field)
        ; ("treePathIndices_i8", field)
        ; ("treePathIndices_i9", field)
        ; ("treePathIndices_i10", field)
        ; ("treePathIndices_i11", field)
        ; ("treePathIndices_i12", field)
        ; ("treePathIndices_i13", field)
        ; ("treePathIndices_i14", field)
        ; ("treePathIndices_i15", field)
        ; ("treePathIndices_i16", field)
        ; ("treePathIndices_i17", field)
        ; ("treePathIndices_i18", field)
        ; ("treePathIndices_i19", field)
        ; ("treeSiblings_i0", field)
        ; ("treeSiblings_i1", field)
        ; ("treeSiblings_i2", field)
        ; ("treeSiblings_i3", field)
        ; ("treeSiblings_i4", field)
        ; ("treeSiblings_i5", field)
        ; ("treeSiblings_i6", field)
        ; ("treeSiblings_i7", field)
        ; ("treeSiblings_i8", field)
        ; ("treeSiblings_i9", field)
        ; ("treeSiblings_i10", field)
        ; ("treeSiblings_i11", field)
        ; ("treeSiblings_i12", field)
        ; ("treeSiblings_i13", field)
        ; ("treeSiblings_i14", field)
        ; ("treeSiblings_i15", field)
        ; ("treeSiblings_i16", field)
        ; ("treeSiblings_i17", field)
        ; ("treeSiblings_i18", field)
        ; ("treeSiblings_i19", field) ]
    ; outputs= semaphore_outputs
    ; dep= None
    ; body=
        elet "var0_v1" (F.const 20)
        @@ elet "calculateSecret_dot_identityNullifier"
             (var "identityNullifier")
        @@ elet "calculateSecret_dot_identityTrapdoor" (var "identityTrapdoor")
        @@ elet "calculateSecret_result"
             (call "CalculateSecret"
                [ var "calculateSecret_dot_identityNullifier"
                ; var "calculateSecret_dot_identityTrapdoor" ] )
        @@ elet "calculateSecret_dot_out" (var "calculateSecret_result")
        @@ elet "secret" (var "calculateSecret_dot_out")
        @@ elet "calculateIdentityCommitment_dot_secret" (var "secret")
        @@ elet "calculateIdentityCommitment_result"
             (call "CalculateIdentityCommitment"
                [var "calculateIdentityCommitment_dot_secret"] )
        @@ elet "calculateIdentityCommitment_dot_out"
             (var "calculateIdentityCommitment_result")
        @@ elet "calculateNullifierHash_dot_externalNullifier"
             (var "externalNullifier")
        @@ elet "calculateNullifierHash_dot_identityNullifier"
             (var "identityNullifier")
        @@ elet "calculateNullifierHash_result"
             (call "CalculateNullifierHash"
                [ var "calculateNullifierHash_dot_externalNullifier"
                ; var "calculateNullifierHash_dot_identityNullifier" ] )
        @@ elet "calculateNullifierHash_dot_out"
             (var "calculateNullifierHash_result")
        @@ elet "inclusionProof_dot_leaf"
             (var "calculateIdentityCommitment_dot_out")
        @@ elet "var1_v1" (F.const 0)
        @@ elet "inclusionProof_dot_siblings_i0" (var "treeSiblings_i0")
        @@ elet "inclusionProof_dot_pathIndices_i0" (var "treePathIndices_i0")
        @@ elet "var1_v2" (F.const 666)
        @@ elet "inclusionProof_dot_siblings_i1" (var "treeSiblings_i1")
        @@ elet "inclusionProof_dot_pathIndices_i1" (var "treePathIndices_i1")
        @@ elet "var1_v3" (F.const 666)
        @@ elet "inclusionProof_dot_siblings_i2" (var "treeSiblings_i2")
        @@ elet "inclusionProof_dot_pathIndices_i2" (var "treePathIndices_i2")
        @@ elet "var1_v4" (F.const 666)
        @@ elet "inclusionProof_dot_siblings_i3" (var "treeSiblings_i3")
        @@ elet "inclusionProof_dot_pathIndices_i3" (var "treePathIndices_i3")
        @@ elet "var1_v5" (F.const 666)
        @@ elet "inclusionProof_dot_siblings_i4" (var "treeSiblings_i4")
        @@ elet "inclusionProof_dot_pathIndices_i4" (var "treePathIndices_i4")
        @@ elet "var1_v6" (F.const 666)
        @@ elet "inclusionProof_dot_siblings_i5" (var "treeSiblings_i5")
        @@ elet "inclusionProof_dot_pathIndices_i5" (var "treePathIndices_i5")
        @@ elet "var1_v7" (F.const 666)
        @@ elet "inclusionProof_dot_siblings_i6" (var "treeSiblings_i6")
        @@ elet "inclusionProof_dot_pathIndices_i6" (var "treePathIndices_i6")
        @@ elet "var1_v8" (F.const 666)
        @@ elet "inclusionProof_dot_siblings_i7" (var "treeSiblings_i7")
        @@ elet "inclusionProof_dot_pathIndices_i7" (var "treePathIndices_i7")
        @@ elet "var1_v9" (F.const 666)
        @@ elet "inclusionProof_dot_siblings_i8" (var "treeSiblings_i8")
        @@ elet "inclusionProof_dot_pathIndices_i8" (var "treePathIndices_i8")
        @@ elet "var1_v10" (F.const 666)
        @@ elet "inclusionProof_dot_siblings_i9" (var "treeSiblings_i9")
        @@ elet "inclusionProof_dot_pathIndices_i9" (var "treePathIndices_i9")
        @@ elet "var1_v11" (F.const 666)
        @@ elet "inclusionProof_dot_siblings_i10" (var "treeSiblings_i10")
        @@ elet "inclusionProof_dot_pathIndices_i10" (var "treePathIndices_i10")
        @@ elet "var1_v12" (F.const 666)
        @@ elet "inclusionProof_dot_siblings_i11" (var "treeSiblings_i11")
        @@ elet "inclusionProof_dot_pathIndices_i11" (var "treePathIndices_i11")
        @@ elet "var1_v13" (F.const 666)
        @@ elet "inclusionProof_dot_siblings_i12" (var "treeSiblings_i12")
        @@ elet "inclusionProof_dot_pathIndices_i12" (var "treePathIndices_i12")
        @@ elet "var1_v14" (F.const 666)
        @@ elet "inclusionProof_dot_siblings_i13" (var "treeSiblings_i13")
        @@ elet "inclusionProof_dot_pathIndices_i13" (var "treePathIndices_i13")
        @@ elet "var1_v15" (F.const 666)
        @@ elet "inclusionProof_dot_siblings_i14" (var "treeSiblings_i14")
        @@ elet "inclusionProof_dot_pathIndices_i14" (var "treePathIndices_i14")
        @@ elet "var1_v16" (F.const 666)
        @@ elet "inclusionProof_dot_siblings_i15" (var "treeSiblings_i15")
        @@ elet "inclusionProof_dot_pathIndices_i15" (var "treePathIndices_i15")
        @@ elet "var1_v17" (F.const 666)
        @@ elet "inclusionProof_dot_siblings_i16" (var "treeSiblings_i16")
        @@ elet "inclusionProof_dot_pathIndices_i16" (var "treePathIndices_i16")
        @@ elet "var1_v18" (F.const 666)
        @@ elet "inclusionProof_dot_siblings_i17" (var "treeSiblings_i17")
        @@ elet "inclusionProof_dot_pathIndices_i17" (var "treePathIndices_i17")
        @@ elet "var1_v19" (F.const 666)
        @@ elet "inclusionProof_dot_siblings_i18" (var "treeSiblings_i18")
        @@ elet "inclusionProof_dot_pathIndices_i18" (var "treePathIndices_i18")
        @@ elet "var1_v20" (F.const 666)
        @@ elet "inclusionProof_dot_siblings_i19" (var "treeSiblings_i19")
        @@ elet "inclusionProof_dot_pathIndices_i19" (var "treePathIndices_i19")
        @@ elet "inclusionProof_result"
             (call "MerkleTreeInclusionProof"
                [ var "inclusionProof_dot_leaf"
                ; var "inclusionProof_dot_pathIndices_i0"
                ; var "inclusionProof_dot_pathIndices_i1"
                ; var "inclusionProof_dot_pathIndices_i2"
                ; var "inclusionProof_dot_pathIndices_i3"
                ; var "inclusionProof_dot_pathIndices_i4"
                ; var "inclusionProof_dot_pathIndices_i5"
                ; var "inclusionProof_dot_pathIndices_i6"
                ; var "inclusionProof_dot_pathIndices_i7"
                ; var "inclusionProof_dot_pathIndices_i8"
                ; var "inclusionProof_dot_pathIndices_i9"
                ; var "inclusionProof_dot_pathIndices_i10"
                ; var "inclusionProof_dot_pathIndices_i11"
                ; var "inclusionProof_dot_pathIndices_i12"
                ; var "inclusionProof_dot_pathIndices_i13"
                ; var "inclusionProof_dot_pathIndices_i14"
                ; var "inclusionProof_dot_pathIndices_i15"
                ; var "inclusionProof_dot_pathIndices_i16"
                ; var "inclusionProof_dot_pathIndices_i17"
                ; var "inclusionProof_dot_pathIndices_i18"
                ; var "inclusionProof_dot_pathIndices_i19"
                ; var "inclusionProof_dot_siblings_i0"
                ; var "inclusionProof_dot_siblings_i1"
                ; var "inclusionProof_dot_siblings_i2"
                ; var "inclusionProof_dot_siblings_i3"
                ; var "inclusionProof_dot_siblings_i4"
                ; var "inclusionProof_dot_siblings_i5"
                ; var "inclusionProof_dot_siblings_i6"
                ; var "inclusionProof_dot_siblings_i7"
                ; var "inclusionProof_dot_siblings_i8"
                ; var "inclusionProof_dot_siblings_i9"
                ; var "inclusionProof_dot_siblings_i10"
                ; var "inclusionProof_dot_siblings_i11"
                ; var "inclusionProof_dot_siblings_i12"
                ; var "inclusionProof_dot_siblings_i13"
                ; var "inclusionProof_dot_siblings_i14"
                ; var "inclusionProof_dot_siblings_i15"
                ; var "inclusionProof_dot_siblings_i16"
                ; var "inclusionProof_dot_siblings_i17"
                ; var "inclusionProof_dot_siblings_i18"
                ; var "inclusionProof_dot_siblings_i19" ] )
        @@ elet "inclusionProof_dot_root" (var "inclusionProof_result")
        @@ elet "var1_v21" (F.const 666)
        @@ elet "root" (var "inclusionProof_dot_root")
        @@ elet "signalHashSquared" F.(var "signalHash" * var "signalHash")
        @@ elet "nullifierHash" (var "calculateNullifierHash_dot_out")
        @@ Expr.tuple [var "root"; var "nullifierHash"] }