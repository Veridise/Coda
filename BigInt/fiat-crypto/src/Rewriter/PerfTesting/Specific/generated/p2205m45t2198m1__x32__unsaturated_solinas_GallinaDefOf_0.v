Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  UnsaturatedSolinas.perfGallinaDefOf "2^205-45*2^198-1" 32 0%nat.
  exact I.
Defined.
