Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  UnsaturatedSolinas.perfGallinaAxComputedOf "2^216-2^108-1" 32 1%nat.
  exact I.
Defined.
