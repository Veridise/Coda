open Ast
open Dsl
open Circomlib__Poseidon

let va = v "a"

let b = v "b"

let c = v "c"

let i = v "i"

let k0 = v "k0"

let k1 = v "k1"

let r0 = v "r0"

let r1 = v "r1"

let r2 = v "r2"

let s = v "s"

let t = v "t"

let x = v "x"

let y = v "y"

let z = v "z"

let hasher_out = v "hasher_out"

let vin = v "in"

let in0 = v "in0"

let in1 = v "in1"

let out = v "out"

let out0 = v "out0"

let out1 = v "out1"

let levels = v "levels"

let leaf = v "leaf"

let root = v "root"

let elem = v "elem"

let secret = v "secret"

let address = v "address"

let message = v "message"

let commitment = v "commitment"

let commitmentReceipt = v "commitmentReceipt"

let pathElements = v "pathElements"

let pathIndices = v "pathIndices"

let registryTreeHeight = v "registryTreeHeight"

let accountsTreeHeight = v "accountsTreeHeight"

let sourceIdentifier = v "sourceIdentifier"

let sourceSecret = v "sourceSecret"

let sourceCommitmentReceipt = v "sourceCommitmentReceipt"

let destinationSecret = v "destinationSecret"

let destinationCommitmentReceipt = v "destinationCommitmentReceipt"

let accountMerklePathElements = v "accountMerklePathElements"

let accountMerklePathIndices = v "accountMerklePathIndices"

let accountsTreeRoot = v "accountsTreeRoot"

let registryMerklePathElements = v "registryMerklePathElements"

let registryMerklePathIndices = v "registryMerklePathIndices"

let sourceValue = v "sourceValue"

let destinationIdentifier = v "destinationIdentifier"

let chainId = v "chainId"

let commitmentMapperPubKey = v "commitmentMapperPubKey"

let registryTreeRoot = v "registryTreeRoot"

let externalNullifier = v "externalNullifier"

let nullifier = v "nullifier"

let claimedValue = v "claimedValue"

let accountsTreeValue = v "accountsTreeValue"

let isStrict = v "isStrict"

let accountLeafConstructor = v "accountLeafConstructor"

let registryLeafConstructor = v "registryLeafConstructor"

let sourceSecretHash = v "sourceSecretHash"

(* PositionSwitcher *)

(* forall i o, 2 <= length i /\ 2 <= length o /\ o[0] = i[0] /\ o[1] = i[1] *)
let q_same i o =
  qand
    (qand (qleq z2 (len i)) (qleq z2 (len o)))
    (qand (qeq (get o z0) (get i z0)) (qeq (get o z1) (get i z1)))

(* forall i o, 2 <= length i /\ 2 <= length o /\ o[0] = i[1] /\ o[1] = i[0] *)
let q_switch i o =
  qand
    (qand (qleq z2 (len i)) (qleq z2 (len o)))
    (qand (qeq (get o z0) (get i z1)) (qeq (get o z1) (get i z0)))

(* forall s in nu, binary(s) /\ (s = 1 -> q_switch in nu) /\ (s = 0 -> q_same in nu) *)
let q_out =
  qand (QExpr (is_binary s)) (q_ind s (q_switch vin nu) (q_same vin nu))

(* { Array<F> | q_out(v) /\ length v = 2 } *)
let t_out = tarr_t_q_k tf q_out z2

(* position_switcher (in : { Array<F> | length nu = 2 }) (s : F) : t_out *)
let position_switcher =
  Circuit
    { name= "PositionSwitcher"
    ; inputs= [("in", tarr_tf z2); ("s", tf)]
    ; outputs= [("out", t_out)]
    ; dep= None
    ; body=
        (* s * (1 - s) === 0 *)
        elet "_"
          (assert_eq (fmul s (fsub f1 s)) f0)
          (cons
             (fadd (fmul (fsub (get vin z1) (get vin z0)) s) (get vin z0))
             (cons
                (fadd (fmul (fsub (get vin z0) (get vin z1)) s) (get vin z1))
                cnil ) ) }

(* VerifyMerklePath *)

let u_hasher xs init = unint "VerifyMerklePathHash" [xs; init]

let u_mrkl_tree_incl_pf xs i s = unint "VerifyMerklePathHashProof" [xs; i; s]

(* \i x => #Poseidon 2 (#PositionSwitcher [x; (z[i]).0] (z[i]).1) *)
let lam_vmp z =
  lama "i" tint
    (lama "x" tf
       (elet "y"
          (call "PositionSwitcher"
             [const_array tf [x; tget (get z i) 0]; tget (get z i) 1] )
          (call "Poseidon" [z2; y]) ) )

(* Compute the Poseidon hash over z (list of pairs of F suitable for
   PositionSwitcher) from initial value init *)
let hasher z k init =
  iter z0 k (lam_vmp z) ~init ~inv:(fun i ->
      tfq (qeq nu (u_hasher (u_take i z) init)) )

(* vrfy_mrkl_path
     (levels : { Z | 0 < nu }) (leaf : F) (root : F)
     (pathElements : { Array<F> | length nu = levels })
     (pathIndices : { Array<F> | length nu = levels } : unit *)
let vrfy_mrkl_path =
  Circuit
    { name= "VerifyMerklePath"
    ; inputs=
        [ ("levels", tnat)
        ; ("leaf", tf)
        ; ("root", tf)
        ; ("pathElements", tarr_tf levels)
        ; ("pathIndices", tarr_tf levels) ]
    ; outputs= []
    ; dep= Some (qeq root (u_mrkl_tree_incl_pf leaf pathElements pathIndices))
    ; body=
        (* z = zip pathElements pathIndices *)
        elet "z"
          (zip pathElements pathIndices)
          (* root === hasher z leaf *)
          (elet "hasher_out" (hasher z levels leaf)
             (elet "u" (assert_eq root hasher_out) unit_val) ) }

(** VerifyHydraCommitment *)

let u_hydra_commitment_verifier address secret commitmentMapperPubKey
    commitmentReceipt =
  unint "VerifyHydraCommitment"
    [address; secret; commitmentMapperPubKey; commitmentReceipt]

(* vrfy_hydra_commit
     (address : F) (secret : F)
     (commitmentMapperPubKey : { Array<F> | length nu = 2 })
     (commitmentReceipt : { Array<F> | length nu = 3 }) : unit *)
let vrfy_hydra_commit =
  Circuit
    { name= "VerifyHydraCommitment"
    ; inputs=
        [ ("address", tf)
        ; ("secret", tf)
        ; ("commitmentMapperPubKey", tarr_tf z2)
        ; ("commitmentReceipt", tarr_tf z3) ]
    ; outputs= []
    ; dep=
        Some
          (lift
             (u_hydra_commitment_verifier address secret commitmentMapperPubKey
                commitmentReceipt ) )
    ; body=
        elet "commitment"
          (call "Poseidon" [z1; const_array tf [secret]])
          (elet "message"
             (call "Poseidon" [z2; const_array tf [address; commitment]])
             (elet "k0"
                (get commitmentMapperPubKey z0)
                (elet "k1"
                   (get commitmentMapperPubKey z1)
                   (elet "r2" (get commitmentReceipt z2)
                      (elet "r0" (get commitmentReceipt z0)
                         (elet "r1" (get commitmentReceipt z1)
                            (call "EdDSAPoseidonVerifier"
                               [f1; k0; k1; r2; r0; r1; message] ) ) ) ) ) ) )
    }

(* hydraS1 *)

(* { Z | 252 <= C.k - 1 /\ 0 < nu } *)
let t_h = TRef (tnat, qand (lift (leq z252 (zsub1 CPLen))) (lift (lt z0 nu)))

(* { F | toUZ nu < 2 ^ 252 } *)
let t_claimedValue = tfq (lift (lt (toUZ nu) (zpow z2 z252)))

(* { F | 1 + toUZ nu < 2 ^ 252 } *)
let t_sourceValue = tfq (lift (lt (zadd1 (toUZ nu)) (zpow z2 z252)))

let hydra_s1 =
  Circuit
    { name= "hydraS1"
    ; inputs=
        [ ("registryTreeHeight", t_h)
        ; ("accountsTreeHeight", t_h)
        ; ("sourceIdentifier", tf)
        ; ("sourceSecret", tf)
        ; ("sourceCommitmentReceipt", tarr_tf z3)
        ; ("destinationSecret", tf)
        ; ("destinationCommitmentReceipt", tarr_tf z3)
        ; ("accountMerklePathElements", tarr_tf accountsTreeHeight)
        ; ("accountMerklePathIndices", tarr_tf accountsTreeHeight)
        ; ("accountsTreeRoot", tf)
        ; ("registryMerklePathElements", tarr_tf registryTreeHeight)
        ; ("registryMerklePathIndices", tarr_tf registryTreeHeight)
        ; ("sourceValue", t_sourceValue)
        ; ("destinationIdentifier", tf)
        ; ("chainId", tf)
        ; ("commitmentMapperPubKey", tarr_tf z2)
        ; ("registryTreeRoot", tf)
        ; ("externalNullifier", tf)
        ; ("nullifier", tf)
        ; ("claimedValue", t_claimedValue)
        ; ("accountsTreeValue", tf)
        ; ("isStrict", tf) ]
    ; outputs= []
    ; dep=
        Some
          (ands
             [ (* isStrict = 1 -> claimedValue = sourceValue *)
               qimply (qeq isStrict f1) (qeq claimedValue sourceValue)
             ; (* claimedValue <= sourceValue *)
               qleq (toUZ claimedValue) (toUZ sourceValue)
             ; lift
                 (u_hydra_commitment_verifier sourceIdentifier sourceSecret
                    commitmentMapperPubKey sourceCommitmentReceipt )
             ; lift
                 (u_hydra_commitment_verifier destinationIdentifier
                    destinationSecret commitmentMapperPubKey
                    destinationCommitmentReceipt )
             ; qeq registryTreeRoot
                 (u_mrkl_tree_incl_pf
                    (u_poseidon z2
                       (const_array tf [accountsTreeRoot; accountsTreeValue]) )
                    registryMerklePathElements registryMerklePathIndices )
             ; qeq accountsTreeRoot
                 (u_mrkl_tree_incl_pf
                    (u_poseidon z2
                       (const_array tf [sourceIdentifier; sourceValue]) )
                    accountMerklePathElements accountMerklePathIndices )
             ; qeq nullifier
                 (u_poseidon z2
                    (const_array tf
                       [ u_poseidon z2 (const_array tf [sourceSecret; f1])
                       ; externalNullifier ] ) ) ] )
    ; body=
        elet "u0"
          (call "VerifyHydraCommitment"
             [ sourceIdentifier
             ; sourceSecret
             ; commitmentMapperPubKey
             ; sourceCommitmentReceipt ] )
          (elet "u1"
             (call "VerifyHydraCommitment"
                [ destinationIdentifier
                ; destinationSecret
                ; commitmentMapperPubKey
                ; destinationCommitmentReceipt ] )
             (elet "accountLeafConstructor"
                (call "Poseidon"
                   [z2; const_array tf [sourceIdentifier; sourceValue]] )
                (elet "u2"
                   (call "VerifyMerklePath"
                      [ accountsTreeHeight
                      ; accountLeafConstructor
                      ; accountsTreeRoot
                      ; accountMerklePathElements
                      ; accountMerklePathIndices ] )
                   (elet "registryLeafConstructor"
                      (call "Poseidon"
                         [ z2
                         ; const_array tf [accountsTreeRoot; accountsTreeValue]
                         ] )
                      (elet "u3"
                         (call "VerifyMerklePath"
                            [ registryTreeHeight
                            ; registryLeafConstructor
                            ; registryTreeRoot
                            ; registryMerklePathElements
                            ; registryMerklePathIndices ] )
                         (elet "_x"
                            (call "Num2Bits" [z252; sourceValue])
                            (elet "_y"
                               (call "Num2Bits" [z252; claimedValue])
                               (elet "z"
                                  (call "LessEqThan"
                                     [z252; claimedValue; sourceValue] )
                                  (elet "u4" (assert_eq z f1)
                                     (elet "u5"
                                        (assert_eq
                                           (fmul (fsub1 isStrict) isStrict)
                                           f0 )
                                        (elet "u6"
                                           (assert_eq sourceValue
                                              (fadd sourceValue
                                                 (fmul
                                                    (fsub claimedValue
                                                       sourceValue )
                                                    isStrict ) ) )
                                           (elet "sourceSecretHash"
                                              (call "Poseidon"
                                                 [ z2
                                                 ; const_array tf
                                                     [sourceSecret; f1] ] )
                                              (elet "c"
                                                 (call "Poseidon"
                                                    [ z2
                                                    ; const_array tf
                                                        [ sourceSecretHash
                                                        ; externalNullifier ] ] )
                                                 (elet "u7"
                                                    (assert_eq c nullifier)
                                                    unit_val ) ) ) ) ) ) ) ) ) ) ) ) ) )
    }
