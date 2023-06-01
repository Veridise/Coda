Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  WordByWordMontgomery.perfGallinaDefOf "2^255-19" 64.
  exact I.
Defined.
