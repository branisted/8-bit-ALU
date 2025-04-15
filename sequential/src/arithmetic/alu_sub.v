`timescale 1ns/1ps

module alu_sub(
    input clk,
    input signed [7:0] a, b, 
    input start, 
    output reg signed [15:0] diff
);
    always @(posedge clk) begin
        if (start)
            diff <= a - b;
    end
endmodule