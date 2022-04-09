# VQO

VQO is a Verified Quantum Oracle framework for specifying, testing, and verifying quantum oracles.

## Overview

This repository contains the code used in our draft "Verified Compilation of Quantum Oracles".

**Abstract**: Quantum algorithms often apply classical operations, such as arithmetic or predicate checks, over a quantum superposition of classical data; these so-called *oracles* are often the largest components of a quantum algorithm. To ease the construction of efficient, correct oracle functions, this paper presents VQO, a high-assurance framework implemented with the Coq proof assistant. The core of VQO is OQASM, the *oracle quantum assembly language*. OQASM operations move qubits among three different bases via the Quantum Fourier Transform and Hadamard operations, thus admitting important optimizations, but without inducing *entanglement* and the exponential blowup that comes with it. OQASM's design enabled us to prove correct VQO's compilers---from a simple imperative language called OQIMP to OQASM, and from OQASM to SQIR, a general-purpose quantum assembly language---and allowed us to efficiently test properties of OQASM programs using the QuickChick property-based testing framework. We have used VQO to implement oracles used in Shor's and Grover's algorithms, as well as several common arithmetic operators. VQO's oracles have performance comparable to those produced by Quipper, a state-of-the-art but unverified quantum programming platform.

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
* OQASM.v - OQASM language, type system, and compilation from OQASM to SQIR
* OQASMProof.v - The proofs for the type soundness, language features, and the compilation correctness.
* CLArith.v - "classical" arithmetic operations (including addition, multiplication, subtraction, division, modulo, division-modulo, modulo multiplication, and comparison operations for different combinations, such as if positions are constants or qubits, same below when talking about arithmetic operations) using X and CU gates
* RZArith.v - arithmetic operations using QFT/AQFT and Z axis rotations

OQIMP
* OQIMP.v - OQIMP language, type system, and compilation from OQIMP to OQASM
* OracleExample.v - example oracles written in OQIMP including SHA224, ChaCha20, sin, cos, arcsin, x^n

Testing
* Testing.v - data structures and theorems for random testing
* ArithTesting.v - random testing results for arithmetic operations.

Utilities
* BasicUtility.v - useful helper functions and tactics
* MathSpec.v - abstract specifications for arithmetic operations.
* ExtrOQASM.v - alternate definitions using a gate set suitable for extraction 

The `experiments` directory contains utilities for extracting VQO code & running the experiments in our paper. See the README in that directory for more information.

## Summary of Key Results

### Basic Concepts

* Having a language (OQASM) to describe quantum oracle circuits by using a type system to classify non-entanglement status.
* OQASM is verified to be correct with respect to the compilation to SQIR.
* Be able to run random testing on large quantum oracle circuits.
* Having different implementations of arithmetic operations for TOFF and QFT/AQFT-based.
* Having a random testing framework not only being able to test circuit correctness, but also being able to compare distances between different approximate circuits (based on QFT/AQFT arithmetic implementations), and helping user figuring out the use case of approximate circuits. An example is given as the AQFT modulo circuit in RZArith.v
* Having a high-level OQIMP language that allows users to describe quantum oracle programs based on C-like programs.
* The OQIMP type system is a gradual type system. It labels variables with C or Q modes, where C refers to classical variables and Q refers to quantum variables. We partially evaluate the classical values in OQIMP, then we compile the programs to well-typed circuits in OQASM. The type system in OQASM is semi-dynamic that relies on the classical values to otimize arithmetic circuits efficiently. We are able to implement all arithemtic circuits by using in-place algorithms with effective qubit sizes.
* We implemented many different quantum oracles in OQIMP including SHA224, ChaCha20, sin, cos, arcsin, x^n.
* Having a testing framework based on OQIMP semantics. Users are able to test large programs. The OQIMP semantics is classical so the testing framework can be fast.

### Fully Verified
* Toffoli-based modular multiplication is correct (`modmult_correct` in CLArith.v)
* Compilation from OQASM to SQIR is semantics preserving (`trans_exp_sem` in OQASMProof.v)

### Tested using PBT
* Toffoli-based addition is correct (`tof_add_spec` in ArithTesting.v)
>>>>>>> 0c2d14494eaca7103db85c827661a3378e029c3e
