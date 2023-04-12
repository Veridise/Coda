open Ast
open Dsl
open Circomlib__Poseidon
(* open Typecheck *)

let n = v "n"

let a = v "a"

let b = v "b"

let c = v "c"

let i = v "i"

let j = v "j"

let m = v "m"

let s = v "s"

let x = v "x"

let z = v "z"

let out = v "out"

let nLevels = v "nLevels"

let pathIndices = v "pathIndices"

let siblings = v "siblings"

let root = v "root"

let leaf = v "leaf"

let secret = v "secret"

let identityNullifier = v "identityNullifier"

let identityTrapdoor = v "identityTrapdoor"

let treePathIndices = v "treePathIndices"

let treeSiblings = v "treeSiblings"

let signalHash = v "signalHash"

let externalNullifier = v "externalNullifier"

let nullifierHash = v "nullifierHash"

(* CalculateSecret *)

let t_calc_secret =
  tfq
    (qeq nu
       (u_poseidon z2 (const_array tf [identityNullifier; identityTrapdoor])) )

let calc_secret =
  Circuit
    { name= "CalculateSecret"
    ; inputs= [("identityNullifier", tf); ("identityTrapdoor", tf)]
    ; outputs= [("out", t_calc_secret)]
    ; dep= None
    ; body=
        call "Poseidon"
          [z2; const_array tf [identityNullifier; identityTrapdoor]] }

(* CalculateIdentityCommitment *)

let t_calc_id_commit = tfq (qeq nu (u_poseidon z1 (const_array tf [secret])))

let calc_id_commit =
  Circuit
    { name= "CalculateIdentityCommitment"
    ; inputs= [("secret", tf)]
    ; outputs= [("out", t_calc_id_commit)]
    ; dep= None
    ; body= call "Poseidon" [z1; const_array tf [secret]] }

(* CalculateNullifierHash *)

let t_calc_null_hash =
  tfq
    (qeq nu
       (u_poseidon z2 (const_array tf [externalNullifier; identityNullifier])) )

let calc_null_hash =
  Circuit
    { name= "CalculateNullifierHash"
    ; inputs= [("externalNullifier", tf); ("identityNullifier", tf)]
    ; outputs= [("out", t_calc_null_hash)]
    ; dep= None
    ; body=
        call "Poseidon"
          [z2; const_array tf [externalNullifier; identityNullifier]] }

(* MerkleTreeInclusionProof *)

let u_hasher z init = unint "MrklTreeInclPfHash" [z; init]

let u_zip xs ys = unint "zip" [xs; ys]

let lam_mtip z =
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
                   (const_array (tarr_tf z2)
                      [const_array tf [x; s]; const_array tf [s; x]] )
                   (elet "m"
                      (call "MultiMux1" [z2; c; j])
                      (call "Poseidon" [z2; m]) ) ) ) ) ) )

let hasher z len init =
  iter z0 len (lam_mtip z) ~init ~inv:(fun i ->
      tfq (qeq nu (u_hasher (u_take i z) init)) )

(* {F | nu = #MrklTreeInclPfHash (zip pathIndices siblings) leaf } *)
let t_r = tfq (qeq nu (u_hasher (u_zip pathIndices siblings) leaf))

(* mrkl_tree_incl_pf (nLevels : {Z | 0 <= nu }) (leaf : F)
   (pathIndices : { Array<F> | length nu = nLevels })
   (siblings : { Array<F> | length nu = nLevels }) : t_r *)
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
    ; body= elet "z" (zip pathIndices siblings) (hasher z nLevels leaf) }

(* Semaphore *)

let u_calc_id_commit x = unint "CalculateIdentityCommitment" [x]

let u_calc_secret x y = unint "CalculateSecret" [x; y]

let u_calc_null_hash x y = unint "CalculateNullifierHash" [x; y]

let u_mrkl_tree_incl_pf n xs i s = unint "MerkleTreeInclusionProof" [n; xs; i; s]

(* { F | nu = #MerkleTreeInclusionProof nLevels
         (#CalculateIdentityCommitment (#CalculateSecret identityNullifier identityTrapdoor))
         treePathIndices treeSiblings } *)
let t_semaphore_root =
  tfq
    (qeq nu
       (u_mrkl_tree_incl_pf nLevels
          (u_calc_id_commit (u_calc_secret identityNullifier identityTrapdoor))
          treePathIndices treeSiblings ) )

(* { F | nu =  #CalculateNullifierHash externalNullifier identityNullifier } *)
let t_semaphore_null_hash =
  tfq (qeq nu (u_calc_null_hash externalNullifier identityNullifier))

(* semaphore
     (nLevels : { Z | 0 <= nu }) (identityNullifier : F) (identityTrapdoor : F)
     (treePathIndices : { Array<F> | length nu = nLevels })
     (treeSiblings : { Array<F> | length nu = nLevels })
     (signalHash : F) (externalNullifer : F) : tpair t_semaphore_root t_semaphore_null_hash *)
let semaphore =
  Circuit
    { name= "Semaphore"
    ; inputs=
        [ ("nLevels", tnat)
        ; ("identityNullifier", tf)
        ; ("identityTrapdoor", tf)
        ; ("treePathIndices", tarr_tf nLevels)
        ; ("treeSiblings", tarr_tf nLevels)
        ; ("signalHash", tf)
        ; ("externalNullifier", tf) ]
    ; outputs=
        [("root", t_semaphore_root); ("nullifierHash", t_semaphore_null_hash)]
    ; dep= None
    ; body=
        elet "secret"
          (call "CalculateSecret" [identityNullifier; identityTrapdoor])
          (elet "id_commit"
             (call "CalculateIdentityCommitment" [secret])
             (elet "signalHashSquared"
                (fmul signalHash signalHash)
                (elet "u"
                   (assert_eq (v "signalHashSquared")
                      (fmul signalHash signalHash) )
                   (pair
                      (call "MerkleTreeInclusionProof"
                         [nLevels; v "id_commit"; treePathIndices; treeSiblings] )
                      (call "CalculateNullifierHash"
                         [externalNullifier; identityNullifier] ) ) ) ) ) }
