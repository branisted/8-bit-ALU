`timescale 1ns/1ps

module alu_add(
    input clk, 
    input signed [7:0] a, b, 
    input start, 
    output reg signed [15:0] sum
);
    always @(posedge clk) begin
        if (start)
            sum <= a + b;
    end
endmodule