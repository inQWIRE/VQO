# VQO Experiments

All of the QASM files generated for our paper are available in the vqo_files and quipper_files sub-directories.

## Running VQO

First, run `make` in the top level (`..`) directory. This will compile our Coq proofs. Then run `./extract.sh` in the current directory. This will extract our Coq definitions to OCaml and compile the resulting OCaml code.

Now you can run the VQO experiments with `dune exec --root extraction -- ./run_vqo.exe`. This will generate QASM files with the following naming conventions, where N is the number of bits in the operation:
* cl-adder-N.qasm, rz-adder-N.qasm - computes (x + y) using TOFF-based or QFT-based arithmetic
* rz-const-adder-N.qasm - computes (x + M) using QFT-based arithmetic
* cl-mul-N.qasm, rz-mul-N.qasm - computes (x * y) using TOFF-based or QFT-based arithmetic
* cl-const-mul-N.qasm, rz-const-mul-N.qasm - computes (x * M) using TOFF-based or QFT-based arithmetic
* cl-mod-mul-N.qasm, rz-mod-mul-N.qasm - computes (x * M1 % M2) using TOFF-based or QFT-based arithmetic
* cl-div-mod-N.qasm, rz-div-mod-N.qasm - computes (x mod y, x / y) using TOFF-based or QFT-based arithmetic
* rz-appr-* - approximate versions of various QFT arithmetic circuits
* partial-eval-* - circuits computing (x * y / M), with different degrees of partial evaluation

(These are the same files that are in the vqo_files directory.)

## Using Quipper

Instructions for downloading and installing Quipper are available here: https://www.mathstat.dal.ca/~selinger/quipper/. 

## Informal Testing

You can try simulating the programs in vqo_files or quipper_files with `python sanity_check.py <prog>` (requires Python 3 and `pip install qiskit jkq.ddsim`).

To run these programs through VOQC, clone the [mlvoqc](https://github.com/inQWIRE/mlvoqc) repository and follow the directions there for using `voqc_cli.exe`.
