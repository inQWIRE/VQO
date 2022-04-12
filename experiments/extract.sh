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
rm -f Bin* ClassicalDedekindReals.ml ConstructiveCauchyReals.ml List0.ml \
   QArith_base.ml Rdefinitions.ml Ring_theory.ml Rpow_def.ml Rtrigo1.ml \
   Specif.ml ZArith_dec.ml

# Move the remaining extracted files to the 'ml' subdirectory.
echo "Moving generated files to ml/..."
mv AltGateSet.ml BasicUtility.ml Bool.ml CLArith.ml Datatypes.ml \
   ExtrOQASM.ml FMapList.ml Factorial.ml MathSpec.ml Nat0.ml  \
   OracleExample.ml Order* OQASM* OQIMP.ml PeanoNat.ml Prelim.ml RZArith.ml \
   ml

# Build extracted code.
echo "Building extracted code..."
dune build run_vqo.exe
