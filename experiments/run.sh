dune exec --root extraction -- ./generate_circuits.exe
mv *.qasm vqo_files
echo "Running VOQC optimizations on generated circuits..."
dune exec --root extraction -- ./run_voqc.exe > /dev/null