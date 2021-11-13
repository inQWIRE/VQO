# QVM

**TODO**

## Overview

**TODO**: What are the main theorems proved (and what files are they in)?

## Setup

To compile QVM, you will need [Coq](https://coq.inria.fr/) and the [QuickChick](https://github.com/QuickChick/QuickChick). We strongly recommend using [opam](https://opam.ocaml.org/doc/Install.html) to install Coq and `opam switch` to manage Coq versions. We currently support Coq **version >= 8.12.0**. If you run into errors when compiling our proofs, first check your version of Coq (`coqc -v`).

Assuming you have opam installed (following the instructions in the link above), follow the steps below to set up your environment.
```
# environment setup
opam init
eval $(opam env)

# install some version of the OCaml compiler in a switch named "voqc"
opam switch create voqc 4.12.0
eval $(opam env)

# install Coq -- this will take a while!
opam install coq

# install coq-quickchick
opam install coq-quickchick
```

*Notes*:
* Depending on your system, you may need to replace 4.12.0 in the instructions above with something like "ocaml-base-compiler.4.12.0". Any version of OCaml >= 4.05.0 should be fine. 
* We require Coq version >= 8.12.0. We have tested compilation with 8.12.x and 8.13.x.
* opam error messages and warnings are typically informative, so if you run into trouble then make sure you read the console output.

## Compiling & Running QVM

Run `make` in the top level directory to compile our Coq proofs. See the README in the experiments directory for information on how to run QVM to generate the data in our paper.

## Directory Contents

PQASM
* PQASM.v - PQASM language, type system, and compilation from PQASM to SQIR
* CLArith.v - "classical" arithmetic operations using X and CU gates
* RZArith.v - arithmetic operations using QFT and Z axis rotations

QIMP
* QIMP.v - QIMP language, type system, and compilation from QIMP to PQASM
* OracleExample.v - example oracles written in QIMP including SHA224, sin, cos, arcsin, x^n

Testing
* Testing.v - data structures and theorems for random testing
* ArithTesting.v - random testing results for arithmetic operations and chacha20

Utilities
* BasicUtility.v - useful helper functions and tactics
* MathSpec.v - abstract specifications for arithmetic operations
* AltPQASM.v - alternate definitions using a gate set suitable for extraction 

The `experiments` directory contains utilities for extracting QVM code & running the experiments in our paper. See the README in that directory for more information.
