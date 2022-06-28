Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  WordByWordMontgomery.perfGallinaAxComputedOf "2^205-45*2^198-1" 64.
  exact I.
Defined.
