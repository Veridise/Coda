Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  WordByWordMontgomery.perfPipelineOf "2^384-2^128-2^96+2^32-1" 32.
  exact I.
Defined.
