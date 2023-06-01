Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  UnsaturatedSolinas.perfGallinaAxOf "2^450-2^225-1" 32 0%nat.
  exact I.
Defined.
