Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  UnsaturatedSolinas.perfGallinaAxOf "2^256-4294968273" 32 1%nat.
  exact I.
Defined.
