Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  WordByWordMontgomery.perfPipelineOf "2^256-2^224+2^192+2^96-1" 64.
  exact I.
Defined.
