Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  UnsaturatedSolinas.perfGallinaAxComputedOf "2^384-5*2^368-1" 32 0%nat.
  exact I.
Defined.
