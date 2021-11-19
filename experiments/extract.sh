#!/bin/bash

# Change into the extraction directory.
cd extraction

# Perform extraction.
echo "Extracting code..."
coqc -R ../.. Top Extraction.v

# Remove unneeded files.
echo "Deleting unneeded files..."
rm -f *.glob *.mli *.vo*

# Remove empty/unused files.
rm -f BinNums.ml ClassicalDedekindReals.ml ConstructiveCauchyReals.ml List0.ml \
   QArith_base.ml Rdefinitions.ml Ring_theory.ml Rpow_def.ml Rtrigo1.ml \
   Specif.ml ZArith_dec.ml

# Move the remaining extracted files to the 'ml' subdirectory.
echo "Moving generated files to ml/..."
mv AltGateSet.ml ExtrOQASM.ml BasicUtility.ml Bin*.ml Bool.ml CLArith.ml Datatypes.ml \
   FMapList.ml Factorial.ml MathSpec.ml ModMult.ml Nat0.ml OracleExample.ml \
   Order* OQASM.ml PeanoNat.ml Prelim.ml OQIMP.ml RCIR.ml RZArith.ml \
   ml

# Build extracted code.
echo "Building extracted code..."
dune build run_VQO.exe
