Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  UnsaturatedSolinas.perfGallinaAxComputedOf "2^448-2^224-1" 64 0%nat.
  exact I.
Defined.
