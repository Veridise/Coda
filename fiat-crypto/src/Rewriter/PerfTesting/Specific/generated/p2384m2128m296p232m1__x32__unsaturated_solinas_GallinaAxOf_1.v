Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  UnsaturatedSolinas.perfGallinaAxOf "2^384-2^128-2^96+2^32-1" 32 1%nat.
  exact I.
Defined.
