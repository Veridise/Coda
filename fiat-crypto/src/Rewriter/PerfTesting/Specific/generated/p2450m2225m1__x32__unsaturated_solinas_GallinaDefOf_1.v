Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  UnsaturatedSolinas.perfGallinaDefOf "2^450-2^225-1" 32 1%nat.
  exact I.
Defined.
