# Coda DSL

## Setup

To build the Coda DSL project:
```
cd dsl && dune build
```

To run the typechecker and generate teh Coq lemmas for a specific suite (specified by the test suite name `<suite>`):

```
cd dsl && dune exec -- ./test/test_<suite>.exe
```

This will print (in stdout) the Coq lemmas yielded as obligations to show correctness of the Coda circuits used in the tests (according to the refinement types on the signatures of the circuits). Some of the lemmas are considered trivial, and can be automatically discharged by a tactic `hammer` (developed specifically for Coda). The non-trivial lemmas may also be discharged by `hammer`, but may also require some manual effort. Copy-paste the lemmas in a Coq file with the apropriate imports (see `BigInt/src/Benchmarks` for examples) and prove the non-trivial lemmas yourself.

## Description

`circuit`:
- `name`: The name of the circuit, which is how the circuit is referenced by a `Call` expression.
- `inputs`: The input signals of the circuit, each with an associated refinement type. A call to this circuit as a component incurs obligations to satisfy the refinements of all the inputs. The body of the circuit assumes the refinements of these refinements on the inputs.
- `outputs`: The output signals of the circuit, each with an associated refinement type. A call to this circuit as a component incurs assumptions that the output signal values satisfy these refinements. The body of the circuit is obligated to satisfy these refinements on the outputs.
- `dep`: Deprecated. Just give it `None` during circuit construction.
- `body`: The expression that encodes the output signals' values. If there is only one output signal, then this expression should be of type `{ F | phi }` which is a field element refined by `phi`. If there are multiple (`n > 1`) output signals then this expression should be of type `{ F * ... * F | phi }` which is an `n`-tuple of `F` refined by `phi`.

`QQuant`:
- "Bounded qualifier quantification"
- You can only quantify over integers.
- The start/end index serves as the lower/upper bound.
- `quantification kind * (quantified variable * inclusive starting index * exclusive ending index) * quantified formula`

`Sum`, `Map`:
- Ignore these -- should expand to a user of `Iter` or an uninterpreted function.

`DMatch`:
- "Dependent pattern match"
- `DMatch (matched expr * parameter variabls names * match body)`
- `lama_match` corresponds to `Lambda x . match x with ...`

`Unint`:
- "Uninterpreted function"
- `toSZ`: convert field element into a signed integer
- `toUZ`: convert field element into an unsiged integer

`AscribeUnsafe`:
- This is only used in the type-checker.
- In the synthesis mode.
- Used by `dummy`.

## Development

### To define a circuit

Define a circuit like so:
```
let my_circuit = Circuit
  { name= "MyCircuit";
    inputs= <list of input signals>;
    outputs= <list of output signals>;
    dep= None;
    body= <output> }
```
The list of input signals defines the inputs and their refinements. The list of output signals defines the outputs and their refinements.

When type-checking a circuit, the the inputs parameteres are assumed to have the associated refinements, and the body is asserted to have the associated refinements.

When calling a component of a circuit, the input parameters are asserted to have the associated refinements, and the outputs of the component call are assumed to have the associated refinements.

### To add a new test suite

Let the name of your test suite be `<suite>`.

Defining the test suite circuits:
- Make a new directory `dsl/circuits/<suite>/`.
- Create a new file `dsl/circuits/<suite>/dune`:
```
(library
 (name <suite>)
 (libraries circomlib lib typecheck)
 (modules <list of OCaml modules in dsl/circuits/<suite>/>))
```
- Create new OCaml modules in `dsl/circuits/<suite>/`. These should contain the definitions of the circuits for your test suite.

Defining the test suite tests:
- Create a new file `dsl/test/test_<suite>.ml`
- Modify `dsl/test/dune` to add a new executable with the following form:
```
(executable
  (name test_<suite>)
  (libraries zarith lib coqgen circomlib test_utils <suite>)
  (modules test_<suite>))
```
- For each test, add an invocation in `dsl/test/test_<suite>.ml` in this form, where `<main circuit>` is the circuit to test and `<dependency circuits>` are the circuits that are used as subcomponents of `<main circuit>` (or of each other):
```
let _ = U.test <main circuit> <dependency circuits>
```

To run the new test suite:
```
cd dsl && dune exec -- ./test/test_<suite>.exe
```

### To extend the DSL

If you want to just add a useful alias for constructing terms of the DSL, then put it in `dsl/src/dsl.ml` or `dsl/src/nice_dsl.ml`.

If you actually _do_ want to add a new basic constructor to the DSL's AST, then extend the appropriate data type in `dsl/src/ast.ml`. This will incur some implementation obligations for you to handle:
- in `dsl/src/typecheck.ml`, define the typing rules related to the new construct
- in `dsl/src/coqgen.ml`: define any new rules for converting the new construct to Coq
- if you added any new modules to `dsl/src/`, make sure to include them appropriately in `dsl/src/dune`

## Assumptions

TODO

## Limitations

Coda is based on the features available in Circom 2.0.

Some Circom operations are not directly encoded in Coda.
- Bit shift: bit shifting is not generally translatable to an arithmetic expression, so it is encoded in Coda as an iteration (viz. `num2bits` in `dsl/circuits/circomlib/bitify.ml`)
