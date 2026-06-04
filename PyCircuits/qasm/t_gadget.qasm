OPENQASM 3.0;
include "stdgates.inc";
qubit[2] q;
bit[1] c;
h q[1];
t q[1];
cx q[0], q[1];
c[0] = measure q[1];
if (c[0] == true) s q[0];
