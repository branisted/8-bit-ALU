// The adder used is an Carry Lookahead Adder (CLA) due to the fact that Booth's Multiplication also uses it.

`timescale 1ns / 1ps

module adder (
    input [7:0] A, B,
    input Cin,
    output [7:0] Sum,
    output Cout
);
    wire C4;

    // Lower 4-bit CLA
    cla_4bit cla_low (
        .A(A[3:0]),
        .B(B[3:0]),
        .Cin(Cin),
        .Sum(Sum[3:0]),
        .Cout(C4)
    );

    // Upper 4-bit CLA
    cla_4bit cla_high (
        .A(A[7:4]),
        .B(B[7:4]),
        .Cin(C4),
        .Sum(Sum[7:4]),
        .Cout(Cout)
    );
endmodule