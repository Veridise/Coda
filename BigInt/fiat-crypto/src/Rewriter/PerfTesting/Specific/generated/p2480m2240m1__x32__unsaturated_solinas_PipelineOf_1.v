Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  UnsaturatedSolinas.perfPipelineOf "2^480-2^240-1" 32 1%nat.
  exact I.
Defined.
