`timescale 1ns/1ps

module alu_mul(
    input clk,
    input start,
    input signed [7:0] a, b,
    output reg signed [15:0] product,
    output reg done
);
    always @(posedge clk) begin
        if (start) begin
            product <= a * b;
            done <= 1;
        end else begin
            done <= 0;
        end
    end
endmodule