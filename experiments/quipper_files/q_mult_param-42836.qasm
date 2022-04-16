OPENQASM 2.0;
include "qelib1.inc";

qreg in[16];
qreg anc16[1];
cx in[15],anc16[0];
qreg anc17[1];
qreg anc18[1];
cx in[15],anc18[0];
qreg anc19[1];
x anc18[0];
ccx in[15],anc18[0],anc19[0];
x anc18[0];
cx in[14],anc17[0];
cx anc19[0],anc17[0];
qreg anc20[1];
x anc17[0];
ccx in[14],anc17[0],anc20[0];
x anc17[0];
ccx in[14],anc19[0],anc20[0];
x anc17[0];
ccx anc17[0],anc19[0],anc20[0];
x anc17[0];
cx in[13],anc16[0];
cx anc20[0],anc16[0];
x anc17[0];
ccx anc17[0],anc19[0],anc20[0];
x anc17[0];
ccx in[14],anc19[0],anc20[0];
x anc17[0];
ccx in[14],anc17[0],anc20[0];
x anc17[0];
reset anc20[0];
x anc18[0];
ccx in[15],anc18[0],anc19[0];
x anc18[0];
reset anc19[0];
qreg anc21[1];
cx in[15],anc21[0];
qreg anc22[1];
x anc21[0];
ccx in[15],anc21[0],anc22[0];
x anc21[0];
cx in[14],anc20[0];
cx anc22[0],anc20[0];
qreg anc23[1];
x anc20[0];
ccx in[14],anc20[0],anc23[0];
x anc20[0];
ccx in[14],anc22[0],anc23[0];
x anc20[0];
ccx anc20[0],anc22[0],anc23[0];
x anc20[0];
cx in[13],anc19[0];
cx anc23[0],anc19[0];
qreg anc24[1];
x anc19[0];
ccx in[13],anc19[0],anc24[0];
x anc19[0];
ccx in[13],anc23[0],anc24[0];
x anc19[0];
ccx anc19[0],anc23[0],anc24[0];
x anc19[0];
cx in[12],anc18[0];
cx anc24[0],anc18[0];
qreg anc25[1];
x anc18[0];
ccx in[12],anc18[0],anc25[0];
x anc18[0];
ccx in[12],anc24[0],anc25[0];
x anc18[0];
ccx anc18[0],anc24[0],anc25[0];
x anc18[0];
cx in[11],anc17[0];
cx anc25[0],anc17[0];
qreg anc26[1];
x anc17[0];
ccx in[11],anc17[0],anc26[0];
x anc17[0];
ccx in[11],anc25[0],anc26[0];
x anc17[0];
ccx anc17[0],anc25[0],anc26[0];
x anc17[0];
cx in[10],anc16[0];
cx anc26[0],anc16[0];
x anc17[0];
ccx anc17[0],anc25[0],anc26[0];
x anc17[0];
ccx in[11],anc25[0],anc26[0];
x anc17[0];
ccx in[11],anc17[0],anc26[0];
x anc17[0];
reset anc26[0];
x anc18[0];
ccx anc18[0],anc24[0],anc25[0];
x anc18[0];
ccx in[12],anc24[0],anc25[0];
x anc18[0];
ccx in[12],anc18[0],anc25[0];
x anc18[0];
reset anc25[0];
x anc19[0];
ccx anc19[0],anc23[0],anc24[0];
x anc19[0];
ccx in[13],anc23[0],anc24[0];
x anc19[0];
ccx in[13],anc19[0],anc24[0];
x anc19[0];
reset anc24[0];
x anc20[0];
ccx anc20[0],anc22[0],anc23[0];
x anc20[0];
ccx in[14],anc22[0],anc23[0];
x anc20[0];
ccx in[14],anc20[0],anc23[0];
x anc20[0];
reset anc23[0];
x anc21[0];
ccx in[15],anc21[0],anc22[0];
x anc21[0];
reset anc22[0];
cx in[15],anc22[0];
x anc22[0];
ccx in[15],anc22[0],anc23[0];
x anc22[0];
cx in[14],anc21[0];
cx anc23[0],anc21[0];
x anc21[0];
ccx in[14],anc21[0],anc24[0];
x anc21[0];
ccx in[14],anc23[0],anc24[0];
x anc21[0];
ccx anc21[0],anc23[0],anc24[0];
x anc21[0];
cx in[13],anc20[0];
cx anc24[0],anc20[0];
x anc20[0];
ccx in[13],anc20[0],anc25[0];
x anc20[0];
ccx in[13],anc24[0],anc25[0];
x anc20[0];
ccx anc20[0],anc24[0],anc25[0];
x anc20[0];
cx in[12],anc19[0];
cx anc25[0],anc19[0];
x anc19[0];
ccx in[12],anc19[0],anc26[0];
x anc19[0];
ccx in[12],anc25[0],anc26[0];
x anc19[0];
ccx anc19[0],anc25[0],anc26[0];
x anc19[0];
cx in[11],anc18[0];
cx anc26[0],anc18[0];
qreg anc27[1];
x anc18[0];
ccx in[11],anc18[0],anc27[0];
x anc18[0];
ccx in[11],anc26[0],anc27[0];
x anc18[0];
ccx anc18[0],anc26[0],anc27[0];
x anc18[0];
cx in[10],anc17[0];
cx anc27[0],anc17[0];
qreg anc28[1];
x anc17[0];
ccx in[10],anc17[0],anc28[0];
x anc17[0];
ccx in[10],anc27[0],anc28[0];
x anc17[0];
ccx anc17[0],anc27[0],anc28[0];
x anc17[0];
cx in[9],anc16[0];
cx anc28[0],anc16[0];
x anc17[0];
ccx anc17[0],anc27[0],anc28[0];
x anc17[0];
ccx in[10],anc27[0],anc28[0];
x anc17[0];
ccx in[10],anc17[0],anc28[0];
x anc17[0];
reset anc28[0];
x anc18[0];
ccx anc18[0],anc26[0],anc27[0];
x anc18[0];
ccx in[11],anc26[0],anc27[0];
x anc18[0];
ccx in[11],anc18[0],anc27[0];
x anc18[0];
reset anc27[0];
x anc19[0];
ccx anc19[0],anc25[0],anc26[0];
x anc19[0];
ccx in[12],anc25[0],anc26[0];
x anc19[0];
ccx in[12],anc19[0],anc26[0];
x anc19[0];
reset anc26[0];
x anc20[0];
ccx anc20[0],anc24[0],anc25[0];
x anc20[0];
ccx in[13],anc24[0],anc25[0];
x anc20[0];
ccx in[13],anc20[0],anc25[0];
x anc20[0];
reset anc25[0];
x anc21[0];
ccx anc21[0],anc23[0],anc24[0];
x anc21[0];
ccx in[14],anc23[0],anc24[0];
x anc21[0];
ccx in[14],anc21[0],anc24[0];
x anc21[0];
reset anc24[0];
x anc22[0];
ccx in[15],anc22[0],anc23[0];
x anc22[0];
reset anc23[0];
cx in[15],anc23[0];
x anc23[0];
ccx in[15],anc23[0],anc24[0];
x anc23[0];
cx in[14],anc22[0];
cx anc24[0],anc22[0];
x anc22[0];
ccx in[14],anc22[0],anc25[0];
x anc22[0];
ccx in[14],anc24[0],anc25[0];
x anc22[0];
ccx anc22[0],anc24[0],anc25[0];
x anc22[0];
cx in[13],anc21[0];
cx anc25[0],anc21[0];
x anc21[0];
ccx in[13],anc21[0],anc26[0];
x anc21[0];
ccx in[13],anc25[0],anc26[0];
x anc21[0];
ccx anc21[0],anc25[0],anc26[0];
x anc21[0];
cx in[12],anc20[0];
cx anc26[0],anc20[0];
x anc20[0];
ccx in[12],anc20[0],anc27[0];
x anc20[0];
ccx in[12],anc26[0],anc27[0];
x anc20[0];
ccx anc20[0],anc26[0],anc27[0];
x anc20[0];
cx in[11],anc19[0];
cx anc27[0],anc19[0];
x anc19[0];
ccx in[11],anc19[0],anc28[0];
x anc19[0];
ccx in[11],anc27[0],anc28[0];
x anc19[0];
ccx anc19[0],anc27[0],anc28[0];
x anc19[0];
cx in[10],anc18[0];
cx anc28[0],anc18[0];
qreg anc29[1];
x anc18[0];
ccx in[10],anc18[0],anc29[0];
x anc18[0];
ccx in[10],anc28[0],anc29[0];
x anc18[0];
ccx anc18[0],anc28[0],anc29[0];
x anc18[0];
cx in[9],anc17[0];
cx anc29[0],anc17[0];
qreg anc30[1];
x anc17[0];
ccx in[9],anc17[0],anc30[0];
x anc17[0];
ccx in[9],anc29[0],anc30[0];
x anc17[0];
ccx anc17[0],anc29[0],anc30[0];
x anc17[0];
cx in[8],anc16[0];
cx anc30[0],anc16[0];
x anc17[0];
ccx anc17[0],anc29[0],anc30[0];
x anc17[0];
ccx in[9],anc29[0],anc30[0];
x anc17[0];
ccx in[9],anc17[0],anc30[0];
x anc17[0];
reset anc30[0];
x anc18[0];
ccx anc18[0],anc28[0],anc29[0];
x anc18[0];
ccx in[10],anc28[0],anc29[0];
x anc18[0];
ccx in[10],anc18[0],anc29[0];
x anc18[0];
reset anc29[0];
x anc19[0];
ccx anc19[0],anc27[0],anc28[0];
x anc19[0];
ccx in[11],anc27[0],anc28[0];
x anc19[0];
ccx in[11],anc19[0],anc28[0];
x anc19[0];
reset anc28[0];
x anc20[0];
ccx anc20[0],anc26[0],anc27[0];
x anc20[0];
ccx in[12],anc26[0],anc27[0];
x anc20[0];
ccx in[12],anc20[0],anc27[0];
x anc20[0];
reset anc27[0];
x anc21[0];
ccx anc21[0],anc25[0],anc26[0];
x anc21[0];
ccx in[13],anc25[0],anc26[0];
x anc21[0];
ccx in[13],anc21[0],anc26[0];
x anc21[0];
reset anc26[0];
x anc22[0];
ccx anc22[0],anc24[0],anc25[0];
x anc22[0];
ccx in[14],anc24[0],anc25[0];
x anc22[0];
ccx in[14],anc22[0],anc25[0];
x anc22[0];
reset anc25[0];
x anc23[0];
ccx in[15],anc23[0],anc24[0];
x anc23[0];
reset anc24[0];
cx in[15],anc25[0];
x anc25[0];
ccx in[15],anc25[0],anc26[0];
x anc25[0];
cx in[14],anc24[0];
cx anc26[0],anc24[0];
x anc24[0];
ccx in[14],anc24[0],anc27[0];
x anc24[0];
ccx in[14],anc26[0],anc27[0];
x anc24[0];
ccx anc24[0],anc26[0],anc27[0];
x anc24[0];
cx in[13],anc23[0];
cx anc27[0],anc23[0];
x anc23[0];
ccx in[13],anc23[0],anc28[0];
x anc23[0];
ccx in[13],anc27[0],anc28[0];
x anc23[0];
ccx anc23[0],anc27[0],anc28[0];
x anc23[0];
cx in[12],anc22[0];
cx anc28[0],anc22[0];
x anc22[0];
ccx in[12],anc22[0],anc29[0];
x anc22[0];
ccx in[12],anc28[0],anc29[0];
x anc22[0];
ccx anc22[0],anc28[0],anc29[0];
x anc22[0];
cx in[11],anc21[0];
cx anc29[0],anc21[0];
x anc21[0];
ccx in[11],anc21[0],anc30[0];
x anc21[0];
ccx in[11],anc29[0],anc30[0];
x anc21[0];
ccx anc21[0],anc29[0],anc30[0];
x anc21[0];
cx in[10],anc20[0];
cx anc30[0],anc20[0];
qreg anc31[1];
x anc20[0];
ccx in[10],anc20[0],anc31[0];
x anc20[0];
ccx in[10],anc30[0],anc31[0];
x anc20[0];
ccx anc20[0],anc30[0],anc31[0];
x anc20[0];
cx in[9],anc19[0];
cx anc31[0],anc19[0];
qreg anc32[1];
x anc19[0];
ccx in[9],anc19[0],anc32[0];
x anc19[0];
ccx in[9],anc31[0],anc32[0];
x anc19[0];
ccx anc19[0],anc31[0],anc32[0];
x anc19[0];
cx in[8],anc18[0];
cx anc32[0],anc18[0];
qreg anc33[1];
x anc18[0];
ccx in[8],anc18[0],anc33[0];
x anc18[0];
ccx in[8],anc32[0],anc33[0];
x anc18[0];
ccx anc18[0],anc32[0],anc33[0];
x anc18[0];
cx in[7],anc17[0];
cx anc33[0],anc17[0];
qreg anc34[1];
x anc17[0];
ccx in[7],anc17[0],anc34[0];
x anc17[0];
ccx in[7],anc33[0],anc34[0];
x anc17[0];
ccx anc17[0],anc33[0],anc34[0];
x anc17[0];
cx in[6],anc16[0];
cx anc34[0],anc16[0];
x anc17[0];
ccx anc17[0],anc33[0],anc34[0];
x anc17[0];
ccx in[7],anc33[0],anc34[0];
x anc17[0];
ccx in[7],anc17[0],anc34[0];
x anc17[0];
reset anc34[0];
x anc18[0];
ccx anc18[0],anc32[0],anc33[0];
x anc18[0];
ccx in[8],anc32[0],anc33[0];
x anc18[0];
ccx in[8],anc18[0],anc33[0];
x anc18[0];
reset anc33[0];
x anc19[0];
ccx anc19[0],anc31[0],anc32[0];
x anc19[0];
ccx in[9],anc31[0],anc32[0];
x anc19[0];
ccx in[9],anc19[0],anc32[0];
x anc19[0];
reset anc32[0];
x anc20[0];
ccx anc20[0],anc30[0],anc31[0];
x anc20[0];
ccx in[10],anc30[0],anc31[0];
x anc20[0];
ccx in[10],anc20[0],anc31[0];
x anc20[0];
reset anc31[0];
x anc21[0];
ccx anc21[0],anc29[0],anc30[0];
x anc21[0];
ccx in[11],anc29[0],anc30[0];
x anc21[0];
ccx in[11],anc21[0],anc30[0];
x anc21[0];
reset anc30[0];
x anc22[0];
ccx anc22[0],anc28[0],anc29[0];
x anc22[0];
ccx in[12],anc28[0],anc29[0];
x anc22[0];
ccx in[12],anc22[0],anc29[0];
x anc22[0];
reset anc29[0];
x anc23[0];
ccx anc23[0],anc27[0],anc28[0];
x anc23[0];
ccx in[13],anc27[0],anc28[0];
x anc23[0];
ccx in[13],anc23[0],anc28[0];
x anc23[0];
reset anc28[0];
x anc24[0];
ccx anc24[0],anc26[0],anc27[0];
x anc24[0];
ccx in[14],anc26[0],anc27[0];
x anc24[0];
ccx in[14],anc24[0],anc27[0];
x anc24[0];
reset anc27[0];
x anc25[0];
ccx in[15],anc25[0],anc26[0];
x anc25[0];
reset anc26[0];
cx in[15],anc27[0];
x anc27[0];
ccx in[15],anc27[0],anc28[0];
x anc27[0];
cx in[14],anc26[0];
cx anc28[0],anc26[0];
x anc26[0];
ccx in[14],anc26[0],anc29[0];
x anc26[0];
ccx in[14],anc28[0],anc29[0];
x anc26[0];
ccx anc26[0],anc28[0],anc29[0];
x anc26[0];
cx in[13],anc25[0];
cx anc29[0],anc25[0];
x anc25[0];
ccx in[13],anc25[0],anc30[0];
x anc25[0];
ccx in[13],anc29[0],anc30[0];
x anc25[0];
ccx anc25[0],anc29[0],anc30[0];
x anc25[0];
cx in[12],anc24[0];
cx anc30[0],anc24[0];
x anc24[0];
ccx in[12],anc24[0],anc31[0];
x anc24[0];
ccx in[12],anc30[0],anc31[0];
x anc24[0];
ccx anc24[0],anc30[0],anc31[0];
x anc24[0];
cx in[11],anc23[0];
cx anc31[0],anc23[0];
x anc23[0];
ccx in[11],anc23[0],anc32[0];
x anc23[0];
ccx in[11],anc31[0],anc32[0];
x anc23[0];
ccx anc23[0],anc31[0],anc32[0];
x anc23[0];
cx in[10],anc22[0];
cx anc32[0],anc22[0];
x anc22[0];
ccx in[10],anc22[0],anc33[0];
x anc22[0];
ccx in[10],anc32[0],anc33[0];
x anc22[0];
ccx anc22[0],anc32[0],anc33[0];
x anc22[0];
cx in[9],anc21[0];
cx anc33[0],anc21[0];
x anc21[0];
ccx in[9],anc21[0],anc34[0];
x anc21[0];
ccx in[9],anc33[0],anc34[0];
x anc21[0];
ccx anc21[0],anc33[0],anc34[0];
x anc21[0];
cx in[8],anc20[0];
cx anc34[0],anc20[0];
qreg anc35[1];
x anc20[0];
ccx in[8],anc20[0],anc35[0];
x anc20[0];
ccx in[8],anc34[0],anc35[0];
x anc20[0];
ccx anc20[0],anc34[0],anc35[0];
x anc20[0];
cx in[7],anc19[0];
cx anc35[0],anc19[0];
qreg anc36[1];
x anc19[0];
ccx in[7],anc19[0],anc36[0];
x anc19[0];
ccx in[7],anc35[0],anc36[0];
x anc19[0];
ccx anc19[0],anc35[0],anc36[0];
x anc19[0];
cx in[6],anc18[0];
cx anc36[0],anc18[0];
qreg anc37[1];
x anc18[0];
ccx in[6],anc18[0],anc37[0];
x anc18[0];
ccx in[6],anc36[0],anc37[0];
x anc18[0];
ccx anc18[0],anc36[0],anc37[0];
x anc18[0];
cx in[5],anc17[0];
cx anc37[0],anc17[0];
qreg anc38[1];
x anc17[0];
ccx in[5],anc17[0],anc38[0];
x anc17[0];
ccx in[5],anc37[0],anc38[0];
x anc17[0];
ccx anc17[0],anc37[0],anc38[0];
x anc17[0];
cx in[4],anc16[0];
cx anc38[0],anc16[0];
x anc17[0];
ccx anc17[0],anc37[0],anc38[0];
x anc17[0];
ccx in[5],anc37[0],anc38[0];
x anc17[0];
ccx in[5],anc17[0],anc38[0];
x anc17[0];
reset anc38[0];
x anc18[0];
ccx anc18[0],anc36[0],anc37[0];
x anc18[0];
ccx in[6],anc36[0],anc37[0];
x anc18[0];
ccx in[6],anc18[0],anc37[0];
x anc18[0];
reset anc37[0];
x anc19[0];
ccx anc19[0],anc35[0],anc36[0];
x anc19[0];
ccx in[7],anc35[0],anc36[0];
x anc19[0];
ccx in[7],anc19[0],anc36[0];
x anc19[0];
reset anc36[0];
x anc20[0];
ccx anc20[0],anc34[0],anc35[0];
x anc20[0];
ccx in[8],anc34[0],anc35[0];
x anc20[0];
ccx in[8],anc20[0],anc35[0];
x anc20[0];
reset anc35[0];
x anc21[0];
ccx anc21[0],anc33[0],anc34[0];
x anc21[0];
ccx in[9],anc33[0],anc34[0];
x anc21[0];
ccx in[9],anc21[0],anc34[0];
x anc21[0];
reset anc34[0];
x anc22[0];
ccx anc22[0],anc32[0],anc33[0];
x anc22[0];
ccx in[10],anc32[0],anc33[0];
x anc22[0];
ccx in[10],anc22[0],anc33[0];
x anc22[0];
reset anc33[0];
x anc23[0];
ccx anc23[0],anc31[0],anc32[0];
x anc23[0];
ccx in[11],anc31[0],anc32[0];
x anc23[0];
ccx in[11],anc23[0],anc32[0];
x anc23[0];
reset anc32[0];
x anc24[0];
ccx anc24[0],anc30[0],anc31[0];
x anc24[0];
ccx in[12],anc30[0],anc31[0];
x anc24[0];
ccx in[12],anc24[0],anc31[0];
x anc24[0];
reset anc31[0];
x anc25[0];
ccx anc25[0],anc29[0],anc30[0];
x anc25[0];
ccx in[13],anc29[0],anc30[0];
x anc25[0];
ccx in[13],anc25[0],anc30[0];
x anc25[0];
reset anc30[0];
x anc26[0];
ccx anc26[0],anc28[0],anc29[0];
x anc26[0];
ccx in[14],anc28[0],anc29[0];
x anc26[0];
ccx in[14],anc26[0],anc29[0];
x anc26[0];
reset anc29[0];
x anc27[0];
ccx in[15],anc27[0],anc28[0];
x anc27[0];
reset anc28[0];
cx in[15],anc29[0];
x anc29[0];
ccx in[15],anc29[0],anc30[0];
x anc29[0];
cx in[14],anc28[0];
cx anc30[0],anc28[0];
x anc28[0];
ccx in[14],anc28[0],anc31[0];
x anc28[0];
ccx in[14],anc30[0],anc31[0];
x anc28[0];
ccx anc28[0],anc30[0],anc31[0];
x anc28[0];
cx in[13],anc27[0];
cx anc31[0],anc27[0];
x anc27[0];
ccx in[13],anc27[0],anc32[0];
x anc27[0];
ccx in[13],anc31[0],anc32[0];
x anc27[0];
ccx anc27[0],anc31[0],anc32[0];
x anc27[0];
cx in[12],anc26[0];
cx anc32[0],anc26[0];
x anc26[0];
ccx in[12],anc26[0],anc33[0];
x anc26[0];
ccx in[12],anc32[0],anc33[0];
x anc26[0];
ccx anc26[0],anc32[0],anc33[0];
x anc26[0];
cx in[11],anc25[0];
cx anc33[0],anc25[0];
x anc25[0];
ccx in[11],anc25[0],anc34[0];
x anc25[0];
ccx in[11],anc33[0],anc34[0];
x anc25[0];
ccx anc25[0],anc33[0],anc34[0];
x anc25[0];
cx in[10],anc24[0];
cx anc34[0],anc24[0];
x anc24[0];
ccx in[10],anc24[0],anc35[0];
x anc24[0];
ccx in[10],anc34[0],anc35[0];
x anc24[0];
ccx anc24[0],anc34[0],anc35[0];
x anc24[0];
cx in[9],anc23[0];
cx anc35[0],anc23[0];
x anc23[0];
ccx in[9],anc23[0],anc36[0];
x anc23[0];
ccx in[9],anc35[0],anc36[0];
x anc23[0];
ccx anc23[0],anc35[0],anc36[0];
x anc23[0];
cx in[8],anc22[0];
cx anc36[0],anc22[0];
x anc22[0];
ccx in[8],anc22[0],anc37[0];
x anc22[0];
ccx in[8],anc36[0],anc37[0];
x anc22[0];
ccx anc22[0],anc36[0],anc37[0];
x anc22[0];
cx in[7],anc21[0];
cx anc37[0],anc21[0];
x anc21[0];
ccx in[7],anc21[0],anc38[0];
x anc21[0];
ccx in[7],anc37[0],anc38[0];
x anc21[0];
ccx anc21[0],anc37[0],anc38[0];
x anc21[0];
cx in[6],anc20[0];
cx anc38[0],anc20[0];
qreg anc39[1];
x anc20[0];
ccx in[6],anc20[0],anc39[0];
x anc20[0];
ccx in[6],anc38[0],anc39[0];
x anc20[0];
ccx anc20[0],anc38[0],anc39[0];
x anc20[0];
cx in[5],anc19[0];
cx anc39[0],anc19[0];
qreg anc40[1];
x anc19[0];
ccx in[5],anc19[0],anc40[0];
x anc19[0];
ccx in[5],anc39[0],anc40[0];
x anc19[0];
ccx anc19[0],anc39[0],anc40[0];
x anc19[0];
cx in[4],anc18[0];
cx anc40[0],anc18[0];
qreg anc41[1];
x anc18[0];
ccx in[4],anc18[0],anc41[0];
x anc18[0];
ccx in[4],anc40[0],anc41[0];
x anc18[0];
ccx anc18[0],anc40[0],anc41[0];
x anc18[0];
cx in[3],anc17[0];
cx anc41[0],anc17[0];
qreg anc42[1];
x anc17[0];
ccx in[3],anc17[0],anc42[0];
x anc17[0];
ccx in[3],anc41[0],anc42[0];
x anc17[0];
ccx anc17[0],anc41[0],anc42[0];
x anc17[0];
cx in[2],anc16[0];
cx anc42[0],anc16[0];
x anc17[0];
ccx anc17[0],anc41[0],anc42[0];
x anc17[0];
ccx in[3],anc41[0],anc42[0];
x anc17[0];
ccx in[3],anc17[0],anc42[0];
x anc17[0];
reset anc42[0];
x anc18[0];
ccx anc18[0],anc40[0],anc41[0];
x anc18[0];
ccx in[4],anc40[0],anc41[0];
x anc18[0];
ccx in[4],anc18[0],anc41[0];
x anc18[0];
reset anc41[0];
x anc19[0];
ccx anc19[0],anc39[0],anc40[0];
x anc19[0];
ccx in[5],anc39[0],anc40[0];
x anc19[0];
ccx in[5],anc19[0],anc40[0];
x anc19[0];
reset anc40[0];
x anc20[0];
ccx anc20[0],anc38[0],anc39[0];
x anc20[0];
ccx in[6],anc38[0],anc39[0];
x anc20[0];
ccx in[6],anc20[0],anc39[0];
x anc20[0];
reset anc39[0];
x anc21[0];
ccx anc21[0],anc37[0],anc38[0];
x anc21[0];
ccx in[7],anc37[0],anc38[0];
x anc21[0];
ccx in[7],anc21[0],anc38[0];
x anc21[0];
reset anc38[0];
x anc22[0];
ccx anc22[0],anc36[0],anc37[0];
x anc22[0];
ccx in[8],anc36[0],anc37[0];
x anc22[0];
ccx in[8],anc22[0],anc37[0];
x anc22[0];
reset anc37[0];
x anc23[0];
ccx anc23[0],anc35[0],anc36[0];
x anc23[0];
ccx in[9],anc35[0],anc36[0];
x anc23[0];
ccx in[9],anc23[0],anc36[0];
x anc23[0];
reset anc36[0];
x anc24[0];
ccx anc24[0],anc34[0],anc35[0];
x anc24[0];
ccx in[10],anc34[0],anc35[0];
x anc24[0];
ccx in[10],anc24[0],anc35[0];
x anc24[0];
reset anc35[0];
x anc25[0];
ccx anc25[0],anc33[0],anc34[0];
x anc25[0];
ccx in[11],anc33[0],anc34[0];
x anc25[0];
ccx in[11],anc25[0],anc34[0];
x anc25[0];
reset anc34[0];
x anc26[0];
ccx anc26[0],anc32[0],anc33[0];
x anc26[0];
ccx in[12],anc32[0],anc33[0];
x anc26[0];
ccx in[12],anc26[0],anc33[0];
x anc26[0];
reset anc33[0];
x anc27[0];
ccx anc27[0],anc31[0],anc32[0];
x anc27[0];
ccx in[13],anc31[0],anc32[0];
x anc27[0];
ccx in[13],anc27[0],anc32[0];
x anc27[0];
reset anc32[0];
x anc28[0];
ccx anc28[0],anc30[0],anc31[0];
x anc28[0];
ccx in[14],anc30[0],anc31[0];
x anc28[0];
ccx in[14],anc28[0],anc31[0];
x anc28[0];
reset anc31[0];
x anc29[0];
ccx in[15],anc29[0],anc30[0];
x anc29[0];
reset anc30[0];

