Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  UnsaturatedSolinas.perfGallinaDefOf "2^322-2^161-1" 64 1%nat.
  exact I.
Defined.
