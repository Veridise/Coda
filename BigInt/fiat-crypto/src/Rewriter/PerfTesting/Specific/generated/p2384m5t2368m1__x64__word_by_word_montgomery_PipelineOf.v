Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  WordByWordMontgomery.perfPipelineOf "2^384-5*2^368-1" 64.
  exact I.
Defined.
