open Ast
open Core
open Big_int_Z
open Dsl

let tref t q = TRef (t, q)

let ( #: ) = tfq
