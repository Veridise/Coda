Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  WordByWordMontgomery.perfPipelineOf "2^222-117" 32.
  exact I.
Defined.
