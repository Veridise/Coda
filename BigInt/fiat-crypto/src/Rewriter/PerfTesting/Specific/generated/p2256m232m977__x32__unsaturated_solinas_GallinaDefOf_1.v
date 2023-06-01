Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  UnsaturatedSolinas.perfGallinaDefOf "2^256-2^32-977" 32 1%nat.
  exact I.
Defined.
