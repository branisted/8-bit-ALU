`timescale 1ns / 1ps

module cla_8bit (
    input signed [7:0] a, b,
    input cin,
    output signed [7:0] sum,
    output cout
);
    wire c4;

    // Lower 4-bit CLA
    cla_4bit cla_low (
        .A(a[3:0]),
        .B(b[3:0]),
        .Cin(cin),
        .Sum(sum[3:0]),
        .Cout(c4)
    );

    // Upper 4-bit CLA
    cla_4bit cla_high (
        .A(a[7:4]),
        .B(b[7:4]),
        .Cin(c4),
        .Sum(sum[7:4]),
        .Cout(cout)
    );
endmodule