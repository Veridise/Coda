open Ast
open Dsl
open Circomlib__Poseidon
open Notation
(* open Typecheck *)

let identity_secret = v "identity_secret"

let reveal_nonce = v "reveal_nonce"

let attester_id = v "attester_id"

let epoch = v "epoch"

let nonce = v "nonce"

(* EpochKeyHasher *)

let t_epoch_key_hasher identity_secret attester_id epoch nonce =
  tfq
    (qeq nu
       (u_poseidon z2
          (const_array tf
             [ identity_secret
             ; fadds
                 [ attester_id
                 ; fmul (fpow f2 (zn 160)) epoch
                 ; fmul (fpow f2 (zn 208)) nonce ] ] ) ) )

let epoch_key_hasher =
  Circuit
    { name= "EpochKeyHasher"
    ; inputs=
        [ ("identity_secret", tf)
        ; ("attester_id", tf)
        ; ("epoch", tf)
        ; ("nonce", tf) ]
    ; outputs=
        [("out", t_epoch_key_hasher identity_secret attester_id epoch nonce)]
    ; dep= None
    ; body=
        call "Poseidon"
          [ z2
          ; const_array tf
              [ identity_secret
              ; fadds
                  [ attester_id
                  ; fmul (fpow f2 (zn 160)) epoch
                  ; fmul (fpow f2 (zn 208)) nonce ] ] ] }

let field_count = v "FIELD_COUNT"

let lam_eptl =
  lama "i" tint
    (lama "x" tf
       (call "Poseidon" [z2; const_array tf [v "x"; get (v "data") (v "i")]]) )

let u_epoch_tree_leaf a b = unint "u_epoch_tree_leaf" [a; b]

let inv_eptl i =
  tfq (qeq nu (u_epoch_tree_leaf (take (v "data") i) (v "epoch_key")))

let t_epoch_tree_leaf =
  tfq (qeq nu (u_epoch_tree_leaf (v "data") (v "epoch_key")))

let epoch_tree_leaf =
  Circuit
    { name= "EpochTreeLeaf"
    ; inputs=
        [("FIELD_COUNT", tnat); ("epoch_key", tf); ("data", tarr_tf field_count)]
    ; outputs= [("out", t_epoch_tree_leaf)]
    ; dep= None
    ; body= iter z0 field_count lam_eptl ~init:(v "epoch_key") ~inv:inv_eptl }

let data_drop_1 data = drop data z1

let lam_stl =
  lama "i" tint
    (lama "x" tf
       (call "Poseidon"
          [z2; const_array tf [v "x"; get (data_drop_1 (v "data")) (v "i")]] ) )

let u_state_tree_leaf a b = unint "u_state_tree_leaf" [a; b]

let inv_stl i =
  tfq
    (qeq nu
       (u_state_tree_leaf (take (data_drop_1 (v "data")) i) (get (v "data") z0)) )

let t_state_tree_leaf identity_secret attester_id epoch data =
  tfq
    (qeq nu
       (u_poseidon z3
          (const_array tf
             [ identity_secret
             ; fadd attester_id (fmul (fpow f2 (zn 160)) epoch)
             ; u_state_tree_leaf (data_drop_1 data) (get data z0) ] ) ) )

let state_tree_leaf =
  Circuit
    { name= "StateTreeLeaf"
    ; inputs=
        [ ("FIELD_COUNT", tnat)
        ; ("data", tarr_tf field_count)
        ; ("identity_secret", tf)
        ; ("attester_id", tf)
        ; ("epoch", tf) ]
    ; outputs=
        [("out", t_state_tree_leaf identity_secret attester_id epoch (v "data"))]
    ; dep= None
    ; body=
        elet "out1"
          (iter z0 (nsub field_count z1) lam_stl
             ~init:(get (v "data") z0)
             ~inv:inv_stl )
          (call "Poseidon"
             [ z3
             ; const_array tf
                 [ identity_secret
                 ; fadd attester_id (fmul (fpow f2 (zn 160)) epoch)
                 ; v "out1" ] ] ) }

let nullifier = v "nullifier"

let trapdoor = v "trapdoor"

let t_identity_secret =
  tfq (qeq nu (u_poseidon z2 (const_array tf [nullifier; trapdoor])))

let identity_secret1 =
  Circuit
    { name= "IdentitySecret"
    ; inputs= [("nullifier", tf); ("trapdoor", tf)]
    ; outputs= [("out", t_identity_secret)]
    ; dep= None
    ; body= call "Poseidon" [z2; const_array tf [nullifier; trapdoor]] }

let t_identity_commitment_out nullifier trapdoor =
  tfq
    (qeq nu
       (u_poseidon z1
          (const_array tf
             [u_poseidon z2 (const_array tf [nullifier; trapdoor])] ) ) )

let t_identity_commitment_secret nullifier trapdoor =
  tfq (qeq nu (u_poseidon z2 (const_array tf [nullifier; trapdoor])))

let identity_commitment =
  Circuit
    { name= "IdentityCommitment"
    ; inputs= [("nullifier", tf); ("trapdoor", tf)]
    ; outputs=
        [ ("secret", t_identity_commitment_secret nullifier trapdoor)
        ; ("out", t_identity_commitment_out nullifier trapdoor) ]
    ; dep= None
    ; body=
        make
          [ call "IdentitySecret" [nullifier; trapdoor]
          ; call "Poseidon"
              [ z1
              ; const_array tf
                  [u_poseidon z2 (const_array tf [nullifier; trapdoor])] ] ] }

let identity_nullifier = v "identity_nullifier"

let identity_trapdoor = v "identity_trapdoor"

let signup =
  Circuit
    { name= "Signup"
    ; inputs=
        [ ("FIELD_COUNT", tnat)
        ; ("attester_id", tf)
        ; ("epoch", tf)
        ; ("identity_nullifier", tf)
        ; ("identity_trapdoor", tf) ]
    ; outputs=
        [ ( "identity_commitment"
          , t_identity_commitment_out identity_nullifier identity_trapdoor )
        ; ( "state_tree_leaf"
          , t_state_tree_leaf
              (u_poseidon z2
                 (const_array tf [identity_nullifier; identity_trapdoor]) )
              attester_id epoch (v "all_0") ) ]
    ; dep= None
    ; body=
        elet "all_0" (consts_n field_count f0)
          (match_with' ["ic_secret"; "ic_out"]
             (call "IdentityCommitment" [identity_nullifier; identity_trapdoor])
             (make
                [ v "ic_out"
                ; call "StateTreeLeaf"
                    [ v "FIELD_COUNT"
                    ; v "all_0"
                    ; v "ic_secret"
                    ; v "attester_id"
                    ; v "epoch" ] ] ) ) }

let t_epoch_key_hasher_out identity_secret attester_id epoch nonce =
  t_epoch_key_hasher identity_secret attester_id epoch nonce

let t_control reveal_nonce attester_id epoch nonce =
  tfq
    (qeq nu
       (fadds
          [ fmul reveal_nonce (fpow f2 (zn 232))
          ; fmul attester_id (fpow f2 (zn 72))
          ; fmul epoch (fpow f2 (zn 8))
          ; fmul reveal_nonce nonce ] ) )

let epoch_key_lite =
  Circuit
    { name= "EpochKeyLite"
    ; inputs=
        [ ("FIELD_COUNT", tnat)
        ; ( "EPOCH_KEY_NONCE_PER_EPOCH"
          , tnat_e (leq nu (zsub (zpow (zn 2) (zn 8)) z1)) )
        ; ("identity_secret", tf)
        ; ("reveal_nonce", tf)
        ; ("attester_id", tf)
        ; ("epoch", tf)
        ; ("nonce", tf) ]
    ; outputs=
        [ ("control", t_control reveal_nonce attester_id epoch nonce)
        ; ( "epoch_key"
          , t_epoch_key_hasher_out identity_secret attester_id epoch nonce ) ]
    ; dep= None
    ; body=
        elet "reveal_nonce_check"
          (assert_eq (fmul reveal_nonce (fsub reveal_nonce f1)) f0)
          (elet "attester_id_check"
             (call "Num2Bits" [zn 160; v "attester_id"])
             (elet "epoch_bits"
                (call "Num2Bits" [zn 48; v "epoch"])
                (elet "nonce_range_check"
                   (call "Num2Bits" [zn 8; v "nonce"])
                   (elet "nonce_lt"
                      (call "LessThan"
                         [zn 8; v "nonce"; nat2f (v "EPOCH_KEY_NONCE_PER_EPOCH")] )
                      (elet "u0"
                         (assert_eq (v "nonce_lt") f1)
                         (elet "ctrl"
                            (fadds
                               [ fmul reveal_nonce (fpow f2 (zn 232))
                               ; fmul attester_id (fpow f2 (zn 72))
                               ; fmul epoch (fpow f2 (zn 8))
                               ; fmul reveal_nonce nonce ] )
                            (make
                               [ v "ctrl"
                               ; call "EpochKeyHasher"
                                   [ v "identity_secret"
                                   ; v "attester_id"
                                   ; v "epoch"
                                   ; v "nonce" ] ] ) ) ) ) ) ) ) }

let t_alias_check = lift (lt (toUZ (as_le_f (v "in"))) CPrime)

let alias_check =
  Circuit
    { name= "AliasCheck"
    ; inputs= [("in", tarr_t_k tf (zn 254))]
    ; outputs= []
    ; dep= Some t_alias_check
    ; body= unit_val }

let t_n =
  TRef
    ( tint
    , QAnd
        ( lift (leq z0 nu)
        , qand (lift (nu <=. zn 254)) (lift (zn 254 <=. zsub1 CPLen)) ) )

let t_upper_less_than_out =
  tfq
    (ind_dec nu
       (lt
          (zdiv (toUZ (get (v "in_") (zn 0))) (zpow z2 (nsub (zn 254) (v "n"))))
          (zdiv (toUZ (get (v "in_") (zn 1))) (zpow z2 (nsub (zn 254) (v "n")))) ) )

let upper_less_than =
  Circuit
    { name= "UpperLessThan"
    ; inputs= [("n", t_n); ("in_", tarr_t_k tf z2)]
    ; outputs= [("out", t_upper_less_than_out)]
    ; dep= None
    ; body=
        elet "bits_0"
          (call "Num2Bits" [zn 254; get (v "in_") (zn 0)])
          (elet "bits_1"
             (call "Num2Bits" [zn 254; get (v "in_") (zn 1)])
             (elet "alias0"
                (call "AliasCheck" [v "bits_0"])
                (elet "alias1"
                   (call "AliasCheck" [v "bits_1"])
                   (elet "upper_bits_0"
                      (call "Bits2Num"
                         [v "n"; drop (v "bits_0") (nsub (zn 254) (v "n"))] )
                      (elet "upper_bits_1"
                         (call "Bits2Num"
                            [v "n"; drop (v "bits_1") (nsub (zn 254) (v "n"))] )
                         (elet "lt"
                            (call "LessThan"
                               [v "n"; v "upper_bits_0"; v "upper_bits_1"] )
                            (v "lt") ) ) ) ) ) ) }

let t_repl_field_equal_out =
  tfq
    (ind_dec nu
       (eq
          (zmod
             (toUZ (get (v "in_") (zn 0)))
             (zpow z2 (nsub (zn 254) (v "REPL_NONCE_BITS"))) )
          (zmod
             (toUZ (get (v "in_") (zn 1)))
             (zpow z2 (nsub (zn 254) (v "REPL_NONCE_BITS"))) ) ) )

let repl_field_equal =
  Circuit
    { name= "ReplFieldEqual"
    ; inputs= [("REPL_NONCE_BITS", t_n); ("in_", tarr_t_k tf z2)]
    ; outputs= [("out", t_repl_field_equal_out)]
    ; dep= None
    ; body=
        elet "bits_0"
          (call "Num2Bits" [zn 254; get (v "in_") (zn 0)])
          (elet "bits_1"
             (call "Num2Bits" [zn 254; get (v "in_") (zn 1)])
             (elet "alias0"
                (call "AliasCheck" [v "bits_0"])
                (elet "alias1"
                   (call "AliasCheck" [v "bits_1"])
                   (elet "repl_bits_0"
                      (call "Bits2Num"
                         [ nsub (zn 254) (v "REPL_NONCE_BITS")
                         ; take (v "bits_0")
                             (nsub (zn 254) (v "REPL_NONCE_BITS")) ] )
                      (elet "repl_bits_1"
                         (call "Bits2Num"
                            [ nsub (zn 254) (v "REPL_NONCE_BITS")
                            ; take (v "bits_1")
                                (nsub (zn 254) (v "REPL_NONCE_BITS")) ] )
                         (elet "eq"
                            (call "IsEqual" [v "repl_bits_0"; v "repl_bits_1"])
                            (v "eq") ) ) ) ) ) ) }

let u_hasher z init = unint "MrklTreeInclPfHash" [z; init]

let u_zip xs ys = unint "zip" [xs; ys]

let t_r path_index path_elements identity_secret attester_id epoch data =
  tfq
    (qeq nu
       (u_hasher
          (u_zip path_index path_elements)
          (u_poseidon z3
             (const_array tf
                [ identity_secret
                ; fadd attester_id (fmul (fpow f2 (zn 160)) epoch)
                ; u_state_tree_leaf (data_drop_1 data) (get data z0) ] ) ) ) )

let epoch_key =
  Circuit
    { name= "EpochKey"
    ; inputs=
        [ ("STATE_TREE_DEPTH", t_n)
        ; ("EPOCH_KEY_NONCE_PER_EPOCH", t_n)
        ; ("FIELD_COUNT", t_n)
        ; ("state_tree_indexes", tarr_t_k tf (v "STATE_TREE_DEPTH"))
        ; ("state_tree_elements", tarr_t_k tf (v "STATE_TREE_DEPTH"))
        ; ("identity_secret", tf)
        ; ("reveal_nonce", tf)
        ; ("attester_id", tf)
        ; ("epoch", tf)
        ; ("nonce", tf)
        ; ("data", tarr_t_k tf (v "FIELD_COUNT"))
        ; ("sig_data", tf) ]
    ; outputs=
        [ ( "epoch_key"
          , t_epoch_key_hasher_out identity_secret attester_id epoch nonce )
        ; ( "state_tree_root"
          , t_r (v "state_tree_indexes") (v "state_tree_elements")
              identity_secret attester_id epoch (v "data") )
        ; ("control", t_control reveal_nonce attester_id epoch nonce) ]
    ; dep= None
    ; body=
        elet "leaf_hasher"
          (call "StateTreeLeaf"
             [ v "FIELD_COUNT"
             ; v "data"
             ; v "identity_secret"
             ; v "attester_id"
             ; v "epoch" ] )
          (elet "merkletree"
             (call "MerkleTreeInclusionProof"
                [ v "STATE_TREE_DEPTH"
                ; v "leaf_hasher"
                ; v "state_tree_indexes"
                ; v "state_tree_elements" ] )
             (match_with' ["control"; "epoch_key"]
                (call "EpochKeyLite"
                   [ v "FIELD_COUNT"
                   ; v "EPOCH_KEY_NONCE_PER_EPOCH"
                   ; v "identity_secret"
                   ; v "reveal_nonce"
                   ; v "attester_id"
                   ; v "epoch"
                   ; v "nonce" ] )
                (make [v "epoch_key"; v "merkletree"; v "control"]) ) ) }

(* template PreventDoubleAction(STATE_TREE_DEPTH, EPOCH_KEY_NONCE_PER_EPOCH, FIELD_COUNT) {

       // Global state tree
       signal input state_tree_indexes[STATE_TREE_DEPTH];
       signal input state_tree_elements[STATE_TREE_DEPTH];

       // Global state tree leaf: Identity & user state root
       signal input reveal_nonce;
       signal input attester_id;
       signal input epoch;
       signal input nonce;
       signal output epoch_key;
       signal output state_tree_root;

       // Some arbitrary data to endorse
       signal input sig_data; // public input

       // Optionally reveal nonce, epoch, attester_id
       signal output control;

       signal input identity_nullifier;
       signal input external_nullifier;
       signal output nullifier;

       signal input identity_trapdoor;
       signal output identity_commitment;

       signal input data[FIELD_COUNT];

       /* 1. Compute nullifier */
       component poseidon = Poseidon(2);
       poseidon.inputs[0] <== identity_nullifier;
       poseidon.inputs[1] <== external_nullifier;
       nullifier <== poseidon.out;

        /* 2. Compute identity commitment */
       component commitment = IdentityCommitment();
       commitment.nullifier <== identity_nullifier;
       commitment.trapdoor <== identity_trapdoor;
       identity_commitment <== commitment.out;

       /* 3. Check if user exists in the Global State Tree*/
       // Compute user state tree root
       component leaf_hasher = StateTreeLeaf(FIELD_COUNT);
       leaf_hasher.identity_secret <== commitment.secret;
       leaf_hasher.attester_id <== attester_id;
       leaf_hasher.epoch <== epoch;
       for (var x = 0; x < FIELD_COUNT; x++) {
         leaf_hasher.data[x] <== data[x];
       }

       component merkletree = MerkleTreeInclusionProof(STATE_TREE_DEPTH);
       merkletree.leaf <== leaf_hasher.out;
       for (var i = 0; i < STATE_TREE_DEPTH; i++) {
           merkletree.path_index[i] <== state_tree_indexes[i];
           merkletree.path_elements[i] <== state_tree_elements[i];
       }
       state_tree_root <== merkletree.root;

       /* 4. Check epoch key is valid */
       component epoch_key_lite = EpochKeyLite(EPOCH_KEY_NONCE_PER_EPOCH);
       epoch_key_lite.identity_secret <== commitment.secret;
       epoch_key_lite.reveal_nonce <== reveal_nonce;
       epoch_key_lite.attester_id <== attester_id;
       epoch_key_lite.epoch <== epoch;
       epoch_key_lite.nonce <== nonce;
       epoch_key_lite.sig_data <== sig_data;
       control <== epoch_key_lite.control;
       epoch_key <== epoch_key_lite.epoch_key;
   } *)

let prevent_double_action =
  Circuit
    { name= "PreventDoubleAction"
    ; inputs=
        [ ("STATE_TREE_DEPTH", t_n)
        ; ("EPOCH_KEY_NONCE_PER_EPOCH", t_n)
        ; ("FIELD_COUNT", t_n)
        ; ("state_tree_indexes", tarr_t_k tf (v "STATE_TREE_DEPTH"))
        ; ("state_tree_elements", tarr_t_k tf (v "STATE_TREE_DEPTH"))
        ; ("reveal_nonce", tf)
        ; ("attester_id", tf)
        ; ("epoch", tf)
        ; ("nonce", tf)
        ; ("sig_data", tf)
        ; ("identity_nullifier", tf)
        ; ("external_nullifier", tf)
        ; ("identity_trapdoor", tf)
        ; ("data", tarr_t_k tf (v "FIELD_COUNT")) ]
    ; outputs=
        [ ( "epoch_key"
          , t_epoch_key_hasher_out identity_secret attester_id epoch nonce )
        ; ( "state_tree_root"
          , t_r (v "state_tree_indexes") (v "state_tree_elements")
              identity_secret attester_id epoch (v "data") )
        ; ( "nullifier"
          , tfq
              (qeq nu
                 (u_poseidon z2
                    (const_array tf
                       [v "identity_nullifier"; v "external_nullifier"] ) ) ) )
        ; ( "identity_commitment"
          , t_identity_commitment_out (v "identity_nullifier")
              (v "identity_trapdoor") )
        ; ( "control"
          , t_control (v "reveal_nonce") (v "attester_id") (v "epoch")
              (v "nonce") ) ]
    ; dep= None
    ; body=
        elet "nullifier"
          (call "Poseidon"
             [ zn 2
             ; const_array tf [v "identity_nullifier"; v "external_nullifier"]
             ] )
          (match_with' ["identity_secret"; "out"]
             (call "IdentityCommitment"
                [v "identity_nullifier"; v "identity_trapdoor"] )
             (elet "leaf_hasher"
                (call "StateTreeLeaf"
                   [ v "FIELD_COUNT"
                   ; v "data"
                   ; v "identity_secret"
                   ; v "attester_id"
                   ; v "epoch" ] )
                (elet "merkletree"
                   (call "MerkleTreeInclusionProof"
                      [ v "STATE_TREE_DEPTH"
                      ; v "leaf_hasher"
                      ; v "state_tree_indexes"
                      ; v "state_tree_elements" ] )
                   (match_with' ["control"; "epoch_key"]
                      (call "EpochKeyLite"
                         [ v "FIELD_COUNT"
                         ; v "EPOCH_KEY_NONCE_PER_EPOCH"
                         ; v "identity_secret"
                         ; v "reveal_nonce"
                         ; v "attester_id"
                         ; v "epoch"
                         ; v "nonce" ] )
                      (make
                         [ v "epoch_key"
                         ; v "merkletree"
                         ; v "nullifier"
                         ; v "out"
                         ; v "control" ] ) ) ) ) ) }
