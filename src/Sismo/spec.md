# Specifications of the Hydra circuits

## [Premilinary Definitions](https://github.com/Veridise/Coda/blob/a4873f40ff630a40f9d85bb4b7c4f18115665b6a/src/CircomLib/EdDSA.v#L83-L91)

```ocaml
eddsa_poseidon Ax Ay S R8x R8y M := 
    let hash = poseidons_5(R8x, R8y, Ax, Ay, M) in
    let (dbl1_xout, dbl1_yout)  = BabyDbl Ax Ay in
    let (dbl2_xout, dbl2_yout)  = BabyDbl dbl1_xout dbl1_yout in
    let (dbl3_xout, dbl3_yout)  = BabyDbl dbl2_xout dbl2_yout in
    let (right2_x, right2_y)  = edwards_mult hash dbl3_xout dbl3_yout in
    let (right_x, right_y) = edwards_add R8x R8y right2_x right2_y in
    let (left_x, left_y) = edwards_mult S 5299619240641551281634865583518297030282874472190772894086521144482721001553 16950150798460657717958625567821834550301663161624707787222815936182638968203 in
    left_x = right_x /\ left_y = right_y
```

## Circuit Specifications

### 1. Poseidon(2)

- Input: inputs[2]
- Output: out
- Property:
  - (1) forall inputs out1 out2, (poseidons_2 inputs = out1 /\ poseidon_2 inputs = out2) -> out1 = out2

*This property was proved using Picus, an in house tool used to verify that ZK circuits are properly constrained. Picus proved Poseidon(1) and Poseidon(2) were properly constrained and since all properly constrained circuits are deterministic, we can safely conclude that Poseidon(1) and Poseidon(2) are deterministic. 

### 2. [EdDSAPoseidonVerifier()](https://github.com/Veridise/Coda/blob/a4873f40ff630a40f9d85bb4b7c4f18115665b6a/src/CircomLib/EdDSA.v#L93-L111)

- Description: EdDSAPoseidonVerifier is a circuit that verifies an EdDSA signature on a message using the Poseidon hash function. The circuit is disabled when enabled = 0.
- Input: enabled, Ax, Ay, S, R8x, R8y, M
- Precondition: True
- [Postcondition](https://github.com/Veridise/Coda/blob/a4873f40ff630a40f9d85bb4b7c4f18115665b6a/src/CircomLib/EdDSA.v#L131-L158):
  - (1)enabled != 0 -> eddsa_poseidon Ax Ay S R8x R8y M
- [Property](https://github.com/Veridise/Coda/blob/a4873f40ff630a40f9d85bb4b7c4f18115665b6a/src/CircomLib/EdDSA.v#L163-L207):
    (1)(circuit is disabled when enabled = 0) forall Ax Ay S R8x R8y M, EdDSAPoseidonVerifier 0 Ax Ay S R8x R8y M

### 3. [PositionSwitcher](https://github.com/Veridise/Coda/blob/a4873f40ff630a40f9d85bb4b7c4f18115665b6a/src/Sismo/hydra.v#L46-L49)

- Input: in[2], s
- Output: out[2]
- Precondition: True
- [Postcondition](https://github.com/Veridise/Coda/blob/a4873f40ff630a40f9d85bb4b7c4f18115665b6a/src/Sismo/hydra.v#L57-L81):
  - (1) s is binary
  - (2) out[0] = s ? in[1] : in[0]
  - (3) out[1] = s ? in[0] : in[1]

### 4. [VerifyMerklePath(levels)](https://github.com/Veridise/Coda/blob/a4873f40ff630a40f9d85bb4b7c4f18115665b6a/src/Sismo/hydra.v#L104-L116)

- Input: leaf, root, enabled, pathElements[levels], pathIndices[levels]
- Precondition: True
- [Postcondition](https://github.com/Veridise/Coda/blob/a4873f40ff630a40f9d85bb4b7c4f18115665b6a/src/Sismo/hydra.v#L128-L234):
  - (1) forall i, 0 <= i < levels -> pathIndices[i] is binary
  - (2) enabled != 0 -> 
        root = foldl (fun x y => if (fst x = 0) then (poseidons_2 y (snd x)) else (poseidons_2 (snd x) y)) 
            (combine pathIndices pathElements) leaf
- [Property](https://github.com/Veridise/Coda/blob/a4873f40ff630a40f9d85bb4b7c4f18115665b6a/src/Sismo/hydra.v#L236-L254):
  (1)(circuit is disabled when enabled = 0) forall leaf root pathElements pathIndices, VerifyMerklePath leaf root 0 pathElements pathIndices

### 5. [VerifyHydraCommitment](https://github.com/Veridise/Coda/blob/a4873f40ff630a40f9d85bb4b7c4f18115665b6a/src/Sismo/hydra.v#L278-L291)

- Input: address, accountSecret, vaultSecret, enabled, commitmentMapperPubKey[2], commitmentReceipt[3]
- Precondition: True
- [Postcondition](https://github.com/Veridise/Coda/blob/a4873f40ff630a40f9d85bb4b7c4f18115665b6a/src/Sismo/hydra.v#L304-L329): 
  - (1) enabled != 0 ->
        let message = poseidons_2 address (poseidons_2 vaultSecret accountSecret) in 
        eddsa_poseidon commitmentMapperPubKey[0] commitmentMapperPubKey[1] commitmentReceipt[2] commitmentReceipt[0] commitmentReceipt[1] message
- [Property](https://github.com/Veridise/Coda/blob/a4873f40ff630a40f9d85bb4b7c4f18115665b6a/src/Sismo/hydra.v#L333-L360):
  (1)(circuit is disabled when enabled = 0) forall address accountSecret vaultSecret commitmentMapperPubKey commitmentReceipt, VerifyHydraCommitment address accountSecret vaultSecret 0 commitmentMapperPubKey commitmentReceipt

### 6. [hydraS2(registryTreeHeight, accountsTreeHeight)](https://github.com/Veridise/Coda/blob/a4873f40ff630a40f9d85bb4b7c4f18115665b6a/src/Sismo/hydra.v#L388-L458)

- Input: sourceIdentifier, sourceSecret, sourceValue, vaultSecret, sourceCommitmentReceipt[3]
       destinationIdentifier, destinationSecret, destinationCommitmentReceipt[3],
       accountMerklePathElements[accountsTreeHeight], accountMerklePathIndices[accountsTreeHeight], accountsTreeRoot,
       registryMerklePathElements[registryTreeHeight], registryMerklePathIndices[registryTreeHeight], registryTreeRoot,
       extraData, commitmentMapperPubKey[2],
       requestIdentifier, proofIdentifier,
       statementValue, statementComparator, accountsTreeValue,
       vaultIdentifier, vaultNamespace,
       sourceVerificationEnabled, destinationVerificationEnabled
- Precondition: True
- [Postcondition](https://github.com/Veridise/Coda/blob/a4873f40ff630a40f9d85bb4b7c4f18115665b6a/src/Sismo/hydra.v#L490-L635):
  - (1) sourceVerificationEnabled != 0 ->
        let sourceSecretHash = poseidons_2(sourceIdentifier, poseidons_2(vaultSecret, sourceSecret)) in
        eddsa_poseidon commitmentMapperPubKey[0] commitmentMapperPubKey[1] sourceCommitmentReceipt[2] sourceCommitmentReceipt[0] sourceCommitmentReceipt[1] sourceSecretHash
  - (2) destinationVerificationEnabled != 0 ->
        let destinationSecretHash = poseidons_2(destinationIdentifier, poseidons_2(vaultSecret, destinationSecret)) in
        eddsa_poseidon commitmentMapperPubKey[0] commitmentMapperPubKey[1] destinationCommitmentReceipt[2] destinationCommitmentReceipt[0] destinationCommitmentReceipt[1] destinationSecretHash
  - (3) accountsTreeValue != 0 ->
        let leaf = poseidons_2(sourceIdentifier, sourceValue) in
        accountsTreeRoot = foldl (fun x y => if (fst x = 0) then (poseidons_2 y (snd x)) else (poseidons_2 (snd x) y))
                        (combine accountMerklePathIndices accountMerklePathElements) leaf
  - (4) accountsTreeValue != 0 ->
        let leaf = poseidons_2(accountsTreeRoot, accountsTreeValue) in
        registryTreeRoot = foldl (fun x y => if (fst x = 0) then (poseidons_2 y (snd x)) else (poseidons_2 (snd x) y))
                        (combine registryMerklePathIndices registryMerklePathElements) leaf
  - (5) sourceValue < 2^252 /\ statementValue < 2^252 /\ 0 <= statementValue <= sourceValue
  - (6) statementComparator = 1 -> statementValue = sourceValue
  - (7) requestIdentifier != 0 -> proofIdentifier = poseidons_2(poseidons_2(sourceSecret, 1), requestIdentifier)
  - (8) vaultNamespace != 0 -> vaultIdentifier = poseidons_2(vaultSecret, vaultNamespace)

## Current Status

| Circuit | Specified? | Encoded? | Proved? |
| ------- | ---------- | -------- | ------- |
| Poseidon(2) | Yes | - | Yes(Using Picus) |
| EdDSAPoseidonVerifier() | Yes | Yes | Yes |
| PositionSwitcher | Yes | Yes | Yes |
| VerifyMerklePath(levels) | Yes | Yes | Yes |
| VerifyHydraCommitment | Yes | Yes | Yes |
| hydraS2(registryTreeHeight, accountsTreeHeight) | Yes | Yes | Yes |