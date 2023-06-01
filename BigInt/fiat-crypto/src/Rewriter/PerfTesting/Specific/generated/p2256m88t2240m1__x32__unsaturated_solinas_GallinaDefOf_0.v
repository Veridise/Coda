Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  UnsaturatedSolinas.perfGallinaDefOf "2^256-88*2^240-1" 32 0%nat.
  exact I.
Defined.
