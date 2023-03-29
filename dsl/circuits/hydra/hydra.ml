open Ast
open Dsl

let c = v "c"

let i = v "i"

let s = v "s"

let x = v "x"

let z = v "z"

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

(* 2 <= length i /\ 2 <= length o /\ o[0] = i[0] /\ o[1] = i[1] *)
let q_same i o =
  qand
    (qand (qleq z2 (len i)) (qleq z2 (len o)))
    (qand (qeq (get o z0) (get i z0)) (qeq (get o z1) (get i z1)))

(* 2 <= length i /\ 2 <= length o /\ o[0] = i[1] /\ o[1] = i[0] *)
let q_switch i o =
  qand
    (qand (qleq z2 (len i)) (qleq z2 (len o)))
    (qand (qeq (get o z0) (get i z1)) (qeq (get o z1) (get i z0)))

(* binary(s) -> (s = 1 -> q_switch in out) /\ (s = 0 -> q_same in out) *)
let q_out =
  qimply (QExpr (is_binary s)) (q_ind s (q_switch vin nu) (q_same vin nu))

(* { Array<F> | q_out(v) /\ length v = 2 } *)
let t_out = tarr_t_q_k tf q_out z2

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
          (elet "in0" (get vin z0)
             (elet "in1" (get vin z1)
                (* out[0] === (in[1] - in[0]) * s + in[0] *)
                (elet "out0"
                   (fadd (fmul (fsub in1 in0) s) in0)
                   (* out[1] === (in[0] - in[1]) * s + in[1] *)
                   (elet "out1"
                      (fadd (fmul (fsub in0 in1) s) in1)
                      (cons out0 (cons out1 cnil)) ) ) ) ) }

(* let check_position_switcher = typecheck_circuit d_empty position_switcher *)

(* VerifyMerklePath *)

(* \i x => #Poseidon 2 (#PositionSwitcher [x; (z[i]).0] (z[i]).1) *)
let lam_vmp z =
  lama "i" tint
    (lama "x" tf
       (elet "elem"
          (tget (get z i) 0)
          (elet "s"
             (tget (get z i) 1)
             (elet "c"
                (cons x (cons elem cnil))
                (call "Poseidon" [z2; call "PositionSwitcher" [c; s]]) ) ) ) )

(* Compute the Poseidon hash over z (list of pairs of F suitable for
   PositionSwitcher) from initial value init *)
let rec hasher z init =
  iter z0 (len z) (lam_vmp z) ~init ~inv:(fun i ->
      tfq (qeq nu (hasher (take i z) init)) )

let vrfy_mrkl_path =
  Circuit
    { name= "VerifyMerklePath"
    ; inputs=
        [ ("levels", tpos)
        ; ("leaf", tf)
        ; ("root", tf)
        ; ("pathElements", tarr_tf levels)
        ; ("pathIndices", tarr_tf levels) ]
    ; outputs= []
    ; dep= None
    ; body=
        (* z = zip pathElements pathIndices *)
        elet "z"
          (zip pathElements pathIndices)
          (* root === hasher z leaf *)
          (assert_eq root (hasher z leaf)) }

(** VerifyHydraCommitment *)

let vrfy_hydra_commit =
  Circuit
    { name= "VerifyHydraCommitment"
    ; inputs=
        [ ("address", tf)
        ; ("secret", tf)
        ; ("commitmentMapperPubKey", tarr_tf z2)
        ; ("commitmentReceipt", tarr_tf z3) ]
    ; outputs= []
    ; dep= None
    ; body=
        elet "commitment"
          (call "Poseidon" [z1; cons secret cnil])
          (elet "message"
             (call "Poseidon" [z2; cons address (cons commitment cnil)])
             (call "EdDSAPoseidonVerifier"
                [ f1
                ; get commitmentMapperPubKey z0
                ; get commitmentMapperPubKey z1
                ; get commitmentReceipt z2
                ; get commitmentReceipt z0
                ; get commitmentReceipt z1
                ; message ] ) ) }

(* hydraS1 *)

let hydra_s1 =
  Circuit
    { name= "hydraS1"
    ; inputs=
        [ ("registryTreeHeight", tpos)
        ; ("accountsTreeHeight", tpos)
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
        ; ("sourceValue", tf)
        ; ("destinationIdentifier", tf)
        ; ("chainId", tf)
        ; ("commitmentMapperPubKey", tarr_tf z2)
        ; ("registryTreeRoot", tf)
        ; ("externalNullifier", tf)
        ; ("nullifier", tf)
        ; ("claimedValue", tf)
        ; ("accountsTreeValue", tf)
        ; ("isStrict", tf) ]
    ; outputs= []
    ; dep= None
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
                   [z2; cons sourceIdentifier (cons sourceValue cnil)] )
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
                         ; cons accountsTreeRoot (cons accountsTreeValue cnil)
                         ] )
                      (elet "u3"
                         (call "VerifyMerklePath"
                            [ registryTreeHeight
                            ; registryLeafConstructor
                            ; registryTreeRoot
                            ; registryMerklePathElements
                            ; registryMerklePathIndices ] )
                         (elet "_"
                            (call "Num2Bits" [z252; sourceValue])
                            (elet "_"
                               (call "Num2Bits" [z252; claimedValue])
                               (elet "u4"
                                  (assert_eq
                                     (call "LessEqThan"
                                        [ z252
                                        ; cons claimedValue
                                            (cons sourceValue cnil) ] )
                                     f1 )
                                  (elet "u5"
                                     (assert_eq
                                        (fmul (fsub1 isStrict) isStrict)
                                        f0 )
                                     (elet "u6"
                                        (assert_eq sourceValue
                                           (fadd sourceValue
                                              (fmul
                                                 (fsub claimedValue sourceValue)
                                                 isStrict ) ) )
                                        (elet "sourceSecretHash"
                                           (call "Poseidon"
                                              [ z2
                                              ; cons sourceSecret (cons f1 cnil)
                                              ] )
                                           (assert_eq
                                              (call "Poseidon"
                                                 [ z2
                                                 ; cons sourceSecretHash
                                                     (cons externalNullifier
                                                        cnil ) ] )
                                              nullifier ) ) ) ) ) ) ) ) ) ) ) )
    }
