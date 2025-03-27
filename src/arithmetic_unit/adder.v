// The adder used is an Carry Lookahead Adder (CLA) due to the fact that Booth's Multiplication also uses it.

module adder (
    input [7:0] A, B,
    input Cin,
    output [7:0] Sum,
    output Cout
);
    // Propagate and Generate
    wire [7:0] P, G;

    // Internal carries
    wire [7:0] C;

    // Propagate
    assign P = A ^ B;

    // Generate
    assign G = A & B;

    // Carry Lookahead Logic
    assign C[0] = Cin;
    assign C[1] = G[0] | (P[0] & C[0]);
    assign C[2] = G[1] | (P[1] & C[1]);
    assign C[3] = G[2] | (P[2] & C[2]);
    assign C[4] = G[3] | (P[3] & C[3]);
    assign C[5] = G[4] | (P[4] & C[4]);
    assign C[6] = G[5] | (P[5] & C[5]);
    assign C[7] = G[6] | (P[6] & C[6]);
    assign Cout = G[7] | (P[7] & C[7]);

    // Sum Calculation
    assign Sum = P ^ C;

endmodule