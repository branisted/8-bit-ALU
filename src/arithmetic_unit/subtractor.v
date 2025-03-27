module subtractor (
    input [7:0] A, B,
    output [7:0] Diff,
    output Cout // Borrow indicator
);
    wire [7:0] B_inv; // One’s complement of B

    // Invert B using the structural Inverter module
    assign B_inv = ~B;

    // Add A and Two’s Complement of B (B_inv + 1) using CLA
    adder CLA_Sub (
        .A(A),
        .B(B_inv),
        .Cin(1'b1), // Adding 1 for two’s complement
        .Sum(Diff),
        .Cout(Cout)  // Borrow indicator
    );

endmodule
