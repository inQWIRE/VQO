# VQO Experiments

All of the QASM files generated for our paper are available in the vqo_files and quipper_files sub-directories.

## Running VQO

First, run `make` in the top level (`..`) directory. This will compile our Coq proofs. Then run `./extract.sh` in the current directory. This will extract our Coq definitions to OCaml and compile the resulting OCaml code.

Now you can run the VQO experiments with `dune exec --root extraction -- ./run_vqo.exe`. This will generate QASM files with the following naming conventions:
* cl-adder-N.qasm, rz-adder-N.qasm - computes (x + y) using a TOFF-based or QFT-based adder
* rz-const-adder-N.qasm - computes (x + N) using a QFT-based adder
* cl-mul-N.qasm, rz-mul-N.qasm - computes (x * y) using a TOFF-based or QFT-based adder
* cl-const-mul-N.qasm, rz-const-mul-N.qasm - computes (x * N) using a TOFF-based or QFT-based adder
* cl-mod-mul-N.qasm, rz-mod-mul-N.qasm, sqir-mod-mul-N.qasm - computes (x * N % M) using a TOFF-based adder, a QFT-based adder, or our original definition in SQIR.

(These are the same files that are in the vqo_files directory.)

## Using Quipper

Instructions for downloading and installing Quipper are available here: https://www.mathstat.dal.ca/~selinger/quipper/. 

## Informal Testing

You can try simulating the programs in vqo_files or quipper_files with `python sanity_check.py <prog>` (requires Python 3 and `pip install qiskit jkq.ddsim`).

To run these programs through VOQC, clone the [mlvoqc](https://github.com/inQWIRE/mlvoqc) repository and follow the directions there for using `voqc_cli.exe`.
