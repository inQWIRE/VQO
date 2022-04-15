# VQO

VQO is a Verified Quantum Oracle framework for specifying, testing, and verifying quantum oracles.

## Overview

This repository contains the code used in our draft "Verified Compilation of Quantum Oracles," available [on arXiv](https://arxiv.org/pdf/2112.06700.pdf).

**Abstract**: Quantum algorithms often apply classical operations, such as arithmetic or predicate checks, over a quantum superposition of classical data; these so-called oracles are often the largest components of a quantum algorithm. To ease the construction of efficient, correct oracle functions, this paper presents VQO, a high-assurance framework implemented with the Coq proof assistant. The core of VQO is OQASM, the oracle quantum assembly language. OQASM operations move qubits between two different bases via the quantum Fourier transform, thus admitting important optimizations, but without inducing entanglement and the exponential blowup that comes with it. OQASM’s design enabled us to prove correct VQO’s compilers—from a simple imperative language called OQIMP to OQASM, and from OQASM to SQIR, a general-purpose quantum assembly language— and allowed us to efficiently test properties of OQASM programs using the QuickChick property-based testing framework. We have used VQO to implement oracles used in Shor’s and Grover’s algorithms, as well as several common arithmetic operators. VQO’s oracles have performance comparable to those produced by Quipper, a state-of-the-art but unverified quantum programming platform.

## Setup

To compile VQO, you will need [Coq](https://coq.inria.fr/) and [QuickChick](https://github.com/QuickChick/QuickChick). We strongly recommend using [opam](https://opam.ocaml.org/doc/Install.html) to install Coq and `opam switch` to manage Coq versions. We currently support Coq **versions 8.12-8.14**.

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
* Depending on your system, you may need to replace 4.12.0 in the instructions above with something like "ocaml-base-compiler.4.12.0". Any recent version of OCaml should be fine. 
* We require Coq version >= 8.12. We have tested compilation with 8.12.2, 8.13.2, and 8.14.0.
* opam error messages and warnings are typically informative, so if you run into trouble then make sure you read the console output.

## Compiling & Running VQO

Run `make` in the top-level directory to compile our Coq proofs. See the README in the experiments directory for information on how to run VQO to generate the data in our paper.

## Directory Contents

OQASM
* OQASM.v - OQASM language, type system, and compilation from OQASM to SQIR.
* OQASMProof.v - Proofs for the type soundness and the compilation correctness.
* CLArith.v - "Classical" arithmetic operations using X and CU gates.
* RZArith.v - Arithmetic operations using QFT/AQFT and z-axis rotations.

PQASM
* PQASM.v - An experimental extension of OQASM that includes the Hadamard and Rz gates.

OQIMP
* OQIMP.v - OQIMP language, type system, and compilation from OQIMP to OQASM.
* OracleExample.v - Example oracles written in OQIMP including SHA224, ChaCha20, sin, cos, arcsin, x^n.

Testing
* Testing.v - Data structures and theorems for random testing.
* ArithTesting.v - Random testing results for arithmetic operations.

Utilities
* BasicUtility.v - Useful helper functions and tactics.
* MathSpec.v - Abstract specifications for arithmetic operations.
* ExtrOQASM.v - Alternate definitions using a gate set suitable for extraction.

The `experiments` directory contains utilities for extracting VQO code & running the experiments in our paper. See the README in that directory for more information.

## Summary of Key Results

### Fully Verified
* OQASM type system is sound (`well_typed_right_mode_pexp` in OQASMProof.v)
* Compilation from OQASM to SQIR is semantics preserving (`trans_exp_sem` in OQASMProof.v)
* Toffoli-based addition is correct (`adder01_sem_carry0` in CLArith.v)
* Toffoli-based constant addition is correct (`adder01_correct_fb` in CLArith.v)
* Toffoli-based subtraction is correct (`subtractor01_sem` in CLArith.v)
* Toffoli-based less-than is correct (`comparator01_sem` in CLArith.v)
* Toffoli-based modular multiplication is correct (`modmult_correct` in CLArith.v)
* QFT-based addition is correct (`rz_full_adder_sem` in RZArith.v)
* QFT-based constant addition is correct (`rz_adder_sem` in RZArith.v)
* QFT-based constant subtraction is correct (`rz_sub_sem` in RZArith.v)
* QFT-based subtraction is correct (`rz_full_sub_sem` in RZArith.v)
* QFT-based less-than is correct (`rz_compare_sem` in RZArith.v)
* QFT-based modular multiplication is correct (`rz_modmult_full_sem` in RZArith.v)
* OQIMP to OQASM compiler is correct (`compile_cexp_sem` in OQIMP.v)

### Tested using PBT
* 16 different arithmetic circuits are randomly tested in ArithTesting.v.
* sha256, Chacha20, sine, cosine, x^n are tested in OracleExample.v.


