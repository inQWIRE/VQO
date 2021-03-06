OPENQASM 2.0;
include "qelib1.inc";

qreg in[32];
cx in[15],in[31];
qreg anc32[1];
x in[31];
ccx in[15],in[31],anc32[0];
x in[31];
cx in[14],in[30];
cx anc32[0],in[30];
qreg anc33[1];
x in[30];
ccx in[14],in[30],anc33[0];
x in[30];
ccx in[14],anc32[0],anc33[0];
x in[30];
ccx in[30],anc32[0],anc33[0];
x in[30];
cx in[13],in[29];
cx anc33[0],in[29];
qreg anc34[1];
x in[29];
ccx in[13],in[29],anc34[0];
x in[29];
ccx in[13],anc33[0],anc34[0];
x in[29];
ccx in[29],anc33[0],anc34[0];
x in[29];
cx in[12],in[28];
cx anc34[0],in[28];
qreg anc35[1];
x in[28];
ccx in[12],in[28],anc35[0];
x in[28];
ccx in[12],anc34[0],anc35[0];
x in[28];
ccx in[28],anc34[0],anc35[0];
x in[28];
cx in[11],in[27];
cx anc35[0],in[27];
qreg anc36[1];
x in[27];
ccx in[11],in[27],anc36[0];
x in[27];
ccx in[11],anc35[0],anc36[0];
x in[27];
ccx in[27],anc35[0],anc36[0];
x in[27];
cx in[10],in[26];
cx anc36[0],in[26];
qreg anc37[1];
x in[26];
ccx in[10],in[26],anc37[0];
x in[26];
ccx in[10],anc36[0],anc37[0];
x in[26];
ccx in[26],anc36[0],anc37[0];
x in[26];
cx in[9],in[25];
cx anc37[0],in[25];
qreg anc38[1];
x in[25];
ccx in[9],in[25],anc38[0];
x in[25];
ccx in[9],anc37[0],anc38[0];
x in[25];
ccx in[25],anc37[0],anc38[0];
x in[25];
cx in[8],in[24];
cx anc38[0],in[24];
qreg anc39[1];
x in[24];
ccx in[8],in[24],anc39[0];
x in[24];
ccx in[8],anc38[0],anc39[0];
x in[24];
ccx in[24],anc38[0],anc39[0];
x in[24];
cx in[7],in[23];
cx anc39[0],in[23];
qreg anc40[1];
x in[23];
ccx in[7],in[23],anc40[0];
x in[23];
ccx in[7],anc39[0],anc40[0];
x in[23];
ccx in[23],anc39[0],anc40[0];
x in[23];
cx in[6],in[22];
cx anc40[0],in[22];
qreg anc41[1];
x in[22];
ccx in[6],in[22],anc41[0];
x in[22];
ccx in[6],anc40[0],anc41[0];
x in[22];
ccx in[22],anc40[0],anc41[0];
x in[22];
cx in[5],in[21];
cx anc41[0],in[21];
qreg anc42[1];
x in[21];
ccx in[5],in[21],anc42[0];
x in[21];
ccx in[5],anc41[0],anc42[0];
x in[21];
ccx in[21],anc41[0],anc42[0];
x in[21];
cx in[4],in[20];
cx anc42[0],in[20];
qreg anc43[1];
x in[20];
ccx in[4],in[20],anc43[0];
x in[20];
ccx in[4],anc42[0],anc43[0];
x in[20];
ccx in[20],anc42[0],anc43[0];
x in[20];
cx in[3],in[19];
cx anc43[0],in[19];
qreg anc44[1];
x in[19];
ccx in[3],in[19],anc44[0];
x in[19];
ccx in[3],anc43[0],anc44[0];
x in[19];
ccx in[19],anc43[0],anc44[0];
x in[19];
cx in[2],in[18];
cx anc44[0],in[18];
qreg anc45[1];
x in[18];
ccx in[2],in[18],anc45[0];
x in[18];
ccx in[2],anc44[0],anc45[0];
x in[18];
ccx in[18],anc44[0],anc45[0];
x in[18];
cx in[1],in[17];
cx anc45[0],in[17];
qreg anc46[1];
x in[17];
ccx in[1],in[17],anc46[0];
x in[17];
ccx in[1],anc45[0],anc46[0];
x in[17];
ccx in[17],anc45[0],anc46[0];
x in[17];
cx in[0],in[16];
cx anc46[0],in[16];
x in[17];
ccx in[17],anc45[0],anc46[0];
x in[17];
ccx in[1],anc45[0],anc46[0];
x in[17];
ccx in[1],in[17],anc46[0];
x in[17];
reset anc46[0];
x in[18];
ccx in[18],anc44[0],anc45[0];
x in[18];
ccx in[2],anc44[0],anc45[0];
x in[18];
ccx in[2],in[18],anc45[0];
x in[18];
reset anc45[0];
x in[19];
ccx in[19],anc43[0],anc44[0];
x in[19];
ccx in[3],anc43[0],anc44[0];
x in[19];
ccx in[3],in[19],anc44[0];
x in[19];
reset anc44[0];
x in[20];
ccx in[20],anc42[0],anc43[0];
x in[20];
ccx in[4],anc42[0],anc43[0];
x in[20];
ccx in[4],in[20],anc43[0];
x in[20];
reset anc43[0];
x in[21];
ccx in[21],anc41[0],anc42[0];
x in[21];
ccx in[5],anc41[0],anc42[0];
x in[21];
ccx in[5],in[21],anc42[0];
x in[21];
reset anc42[0];
x in[22];
ccx in[22],anc40[0],anc41[0];
x in[22];
ccx in[6],anc40[0],anc41[0];
x in[22];
ccx in[6],in[22],anc41[0];
x in[22];
reset anc41[0];
x in[23];
ccx in[23],anc39[0],anc40[0];
x in[23];
ccx in[7],anc39[0],anc40[0];
x in[23];
ccx in[7],in[23],anc40[0];
x in[23];
reset anc40[0];
x in[24];
ccx in[24],anc38[0],anc39[0];
x in[24];
ccx in[8],anc38[0],anc39[0];
x in[24];
ccx in[8],in[24],anc39[0];
x in[24];
reset anc39[0];
x in[25];
ccx in[25],anc37[0],anc38[0];
x in[25];
ccx in[9],anc37[0],anc38[0];
x in[25];
ccx in[9],in[25],anc38[0];
x in[25];
reset anc38[0];
x in[26];
ccx in[26],anc36[0],anc37[0];
x in[26];
ccx in[10],anc36[0],anc37[0];
x in[26];
ccx in[10],in[26],anc37[0];
x in[26];
reset anc37[0];
x in[27];
ccx in[27],anc35[0],anc36[0];
x in[27];
ccx in[11],anc35[0],anc36[0];
x in[27];
ccx in[11],in[27],anc36[0];
x in[27];
reset anc36[0];
x in[28];
ccx in[28],anc34[0],anc35[0];
x in[28];
ccx in[12],anc34[0],anc35[0];
x in[28];
ccx in[12],in[28],anc35[0];
x in[28];
reset anc35[0];
x in[29];
ccx in[29],anc33[0],anc34[0];
x in[29];
ccx in[13],anc33[0],anc34[0];
x in[29];
ccx in[13],in[29],anc34[0];
x in[29];
reset anc34[0];
x in[30];
ccx in[30],anc32[0],anc33[0];
x in[30];
ccx in[14],anc32[0],anc33[0];
x in[30];
ccx in[14],in[30],anc33[0];
x in[30];
reset anc33[0];
x in[31];
ccx in[15],in[31],anc32[0];
x in[31];
reset anc32[0];

