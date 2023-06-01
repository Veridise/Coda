Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  UnsaturatedSolinas.perfGallinaAxOf "2^205-45*2^198-1" 32 1%nat.
  exact I.
Defined.
