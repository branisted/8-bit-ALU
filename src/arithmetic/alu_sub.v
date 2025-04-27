`timescale 1ns/1ps

module alu_sub(
    input clk,
    input signed [7:0] a, b, 
    input start, 
    output reg signed [15:0] diff
);
    wire [7:0] B_complement;
    wire Cin = 1'b1;
    wire Cout;
    wire signed [7:0] cla_diff;

    twos_complement bcomplement (
        .a(b),
        .not_a(B_complement)
    );

    cla_8bit add (
        .A(a),
        .B(B_complement),
        .Cin(Cin),
        .Sum(cla_diff),
        .Cout(Cout)
    );

    always @(posedge clk) begin
        if (start)
            diff <= {{8{cla_diff[7]}}, cla_diff}; // sign-extend 8 -> 16 bits
    end
endmodule