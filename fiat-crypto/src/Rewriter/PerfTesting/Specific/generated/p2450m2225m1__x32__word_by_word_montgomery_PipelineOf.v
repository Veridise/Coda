Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  WordByWordMontgomery.perfPipelineOf "2^450-2^225-1" 32.
  exact I.
Defined.
