Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  UnsaturatedSolinas.perfPipelineOf "2^224-2^96+1" 64 1%nat.
  exact I.
Defined.
