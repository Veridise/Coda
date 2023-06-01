Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  UnsaturatedSolinas.perfPipelineOf "2^256-4294968273" 64 0%nat.
  exact I.
Defined.
