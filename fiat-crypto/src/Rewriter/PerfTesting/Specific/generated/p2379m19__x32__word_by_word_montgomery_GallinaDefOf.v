Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  WordByWordMontgomery.perfGallinaDefOf "2^379-19" 32.
  exact I.
Defined.
