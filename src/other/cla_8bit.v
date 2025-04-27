`timescale 1ns / 1ps

module cla_8bit (
    input signed [7:0] A, B,
    input Cin,
    output signed [7:0] Sum,
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