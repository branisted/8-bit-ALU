// Module 1: 8-bit Inverter (One’s complement of B)
module inverter_8bit (
    input [7:0] B,
    output [7:0] B_inv
);
    assign B_inv = ~B; // Bitwise NOT (One's complement)
endmodule

// Module 2: 8-bit Subtractor using CLA and Inverter
module subtractor_8bit (
    input [7:0] A, B,
    output [7:0] Diff,
    output Cout // Borrow indicator
);
    wire [7:0] B_inv; // One’s complement of B

    // Invert B using the structural Inverter module
    inverter_8bit inv (.B(B), .B_inv(B_inv));

    // Add A and Two’s Complement of B (B_inv + 1) using CLA
    cla_8bit CLA_Sub (
        .A(A),
        .B(B_inv),
        .Cin(1'b1), // Adding 1 for two’s complement
        .Sum(Diff),
        .Cout(Cout)  // Borrow indicator
    );

endmodule
