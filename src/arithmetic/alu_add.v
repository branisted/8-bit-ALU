`timescale 1ns/1ps

module alu_add(
    input clk, 
    input signed [7:0] a, b, 
    input start, 
    output reg signed [15:0] sum
);
    wire signed [7:0] cla_sum;
    wire cla_cout;

    // Instantiate 8-bit CLA
    cla_8bit add_inst(
        .A(a),
        .B(b),
        .Cin(1'b0),
        .Sum(cla_sum),
        .Cout(cla_cout)
    );

    always @(posedge clk) begin
        if (start)
            sum <= {{8{cla_sum[7]}}, cla_sum}; // sign-extend 8 -> 16 bits
    end
endmodule
