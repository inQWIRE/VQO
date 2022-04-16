# Counting the total number of gates in the Grover diffusion operator used with our ChaCha20 oracle
qubits = 512

# toffolis, cnot, toffolis
generalized_toff = (qubits - 1) + 1 + (qubits - 1)

# X, H, gen_toff, H,  X
# Omitting iI because it's omitted in SQIR
reflect_zero = qubits + 1 + generalized_toff + 1 + qubits

# H, reflect, H
diffusion = qubits + reflect_zero + qubits

print(diffusion)
