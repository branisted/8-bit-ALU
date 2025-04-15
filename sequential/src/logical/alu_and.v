`timescale 1ns/1ps

module alu_and(input clk, input [7:0] a, b, input start, output reg [15:0] res);
    always @(posedge clk) begin
        if (start)
            res <= a & b;
    end
endmodule