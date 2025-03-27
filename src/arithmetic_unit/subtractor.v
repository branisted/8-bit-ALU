module subtractor (
    input [7:0] A, B,
    output [7:0] Diff,
    output Borrow
);
    wire [7:0] B_complement;
    wire Cin, Cout;

    assign B_complement = ~B; // Compute bitwise NOT of B
    assign Cin = 1'b1;        // Add 1 for two’s complement

    // Instantiate the CLA Adder to perform A + (~B + 1)
    adder cla_adder (
        .A(A),
        .B(B_complement),
        .Cin(Cin),
        .Sum(Diff),
        .Cout(Cout) // Cout is actually "No Borrow", so we invert it
    );

    assign Borrow = ~Cout; // Invert Cout to get the actual borrow

endmodule
