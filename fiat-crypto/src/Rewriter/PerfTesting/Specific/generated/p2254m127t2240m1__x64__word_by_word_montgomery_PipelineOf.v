Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  WordByWordMontgomery.perfPipelineOf "2^254-127*2^240-1" 64.
  exact I.
Defined.
