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
                   (cons
                      (cons x (cons s cnil))
                      (cons (cons s (cons x cnil)) cnil) )
                   (call "Poseidon" [z2; call "MultiMux1" [z2; c; j]]) ) ) ) ) )

let rec hasher z init =
  iter z0 (len z) (lam_mtip z) ~init ~inv:(fun i ->
      tfq (qeq nu (hasher (take z i) init)) )

let t_r = tfq (qeq nu (hasher (zip pathIndices siblings) leaf))

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
    ; body= elet "z" (zip pathIndices siblings) (assert_eq root (hasher z leaf))
    }

(* Semaphore *)

let t_semaphore_root =
  tfq
    (qeq nu
       (call "MerkleTreeInclusionProof"
          [ nLevels
          ; call "CalculateIdentityCommitment"
              [call "CalculateSecret" [identityNullifier; identityTrapdoor]]
          ; treePathIndices
          ; treeSiblings ] ) )

let t_semaphore_null_hash =
  tfq
    (qeq nu
       (call "CalculateNullifierHash" [externalNullifier; identityNullifier]) )

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
