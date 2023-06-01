Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  UnsaturatedSolinas.perfGallinaAxComputedOf "2^256-2^224+2^192+2^96-1" 64 0%nat.
  exact I.
Defined.
