# VQO

VQO is a Verified Quantum Oracle framework for specifying, testing, and verifying quantum oracles.

## Overview

This repository contains the code used in our draft "Verified Compilation of Quantum Oracles".

**Abstract**:   Quantum algorithms often apply classical operations, such as arithmetic or predicate checks, over a quantum superposition of classical data; these so-called *oracles* are often the largest components of a quantum algorithm. To ease the construction of efficient, correct oracle functions, this paper presents VQO, a high-assurance framework implemented with the Coq proof assistant. The core of VQO is OQASM, the *oracle quantum assembly language*. OQASM operations move qubits among three different bases via the Quantum Fourier Transform and Hadamard operations, thus admitting important optimizations, but without inducing *entanglement* and the exponential blowup that comes with it. OQASM's design enabled us to prove correct VQO's compilers---from a simple imperative language called OQIMP to OQASM, and from OQASM to SQIR, a general-purpose quantum assembly language---and allowed us to efficiently test properties of OQASM programs using the QuickChick property-based testing framework.  We have used VQO to implement oracles used in Shor's and Grover's algorithms, as well as several common arithmetic operators. VQO's oracles have performance comparable to those produced by Quipper, a state-of-the-art but unverified quantum programming platform.

## Setup

To compile VQO, you will need [Coq](https://coq.inria.fr/) and [QuickChick](https://github.com/QuickChick/QuickChick). We strongly recommend using [opam](https://opam.ocaml.org/doc/Install.html) to install Coq and `opam switch` to manage Coq versions. 

Assuming you have opam installed (following the instructions in the link above), follow the steps below to set up your environment.
```
# environment setup
opam init
eval $(opam env)

# install some version of the OCaml compiler in a switch named "vqo"
opam switch create vqo 4.12.0
eval $(opam env)

# install Coq -- this will take a while!
opam install coq

# install coq-quickchick
opam install coq-quickchick
```

*Notes*:
* Depending on your system, you may need to replace 4.12.0 in the instructions above with something like "ocaml-base-compiler.4.12.0". Any version of OCaml >= 4.05.0 should be fine. 
* We have tested compilation with Coq v8.13.2.
* opam error messages and warnings are typically informative, so if you run into trouble then make sure you read the console output.

## Compiling & Running VQO

Run `make` in the top level directory to compile our Coq proofs. See the README in the experiments directory for information on how to run VQO to generate the data in our paper.

## Directory Contents

OQASM
* OQASM.v - OQASM language, type system, and compilation from OQASM to SQIR
* CLArith.v - "classical" arithmetic operations using X and CU gates
* RZArith.v - arithmetic operations using QFT and Z axis rotations

OQIMP
* OQIMP.v - OQIMP language, type system, and compilation from OQIMP to OQASM
* OracleExample.v - example oracles written in OQIMP including SHA224, ChaCha20, sin, cos, arcsin, x^n

Testing
* Testing.v - data structures and theorems for random testing
* ArithTesting.v - random testing results for arithmetic operations

Utilities
* BasicUtility.v - useful helper functions and tactics
* MathSpec.v - abstract specifications for arithmetic operations
* ExtrOQASM.v - alternate definitions using a gate set suitable for extraction 

The `experiments` directory contains utilities for extracting VQO code & running the experiments in our paper. See the README in that directory for more information.
