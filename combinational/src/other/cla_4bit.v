module cla_4bit (
    input [3:0] A, B,
    input Cin,
    output [3:0] Sum,
    output Cout
);
    wire [3:0] G, P, C;
    
    // Generate and Propagate logic
    gp_logic gp0 (A[0], B[0], G[0], P[0]);
    gp_logic gp1 (A[1], B[1], G[1], P[1]);
    gp_logic gp2 (A[2], B[2], G[2], P[2]);
    gp_logic gp3 (A[3], B[3], G[3], P[3]);

    // Carry Lookahead Logic
    carry_lookahead_unit clu (G, P, Cin, C, Cout);
    
    // Sum Calculation
    xor (Sum[0], P[0], Cin);
    xor (Sum[1], P[1], C[1]);
    xor (Sum[2], P[2], C[2]);
    xor (Sum[3], P[3], C[3]);
endmodule