Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  WordByWordMontgomery.perfGallinaAxComputedOf "2^383-31" 32.
  exact I.
Defined.
