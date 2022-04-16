quipper QAddInPlace.hs
quipper QFTAddInPlace.hs
quipper QAddParamInPlace.hs
quipper QMult.hs
quipper QMultParam.hs
quipper QModdivUnsignedInPlace.hs

./QAddInPlace > q_add_in_place
./QFTAddInPlace > qft_add_in_place
./QMult > q_mult
./QModdivUnsignedInPlace > q_moddiv_unsigned_in_place
for i in 1 760 1171 4248 7845 10197 22350 25228 29982 33287 34823 35549 39598 42836 44650 46727 50905 58967 60600 65535
do
  ./QAddParamInPlace $i > "q_add_param_in_place-$i"
  ./QMultParam $i > "q_mult_param-$i"
done

./QasmPrinting q_add_in_place > q_add_in_place.qasm
./QasmPrinting --inline qft_add_in_place > qft_add_in_place.qasm
./QasmPrinting q_mult > q_mult.qasm
./QasmPrinting q_moddiv_unsigned_in_place > q_moddiv_unsigned_in_place.qasm
for i in 1 760 1171 4248 7845 10197 22350 25228 29982 33287 34823 35549 39598 42836 44650 46727 50905 58967 60600 65535
do
  ./QasmPrinting "q_add_param_in_place-$i" > "q_add_param_in_place-$i.qasm"
  ./QasmPrinting "q_mult_param-$i" > "q_mult_param-$i.qasm"
done
