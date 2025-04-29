`timescale 1ns/1ps
// ALU AND
module alu_and (
    input clk,
    input [7:0] a, b,
    input start,
    output reg [15:0] res,
    output reg done
);
    reg started = 0;
    wire [7:0] and_bits = a & b;

    always @(posedge clk) begin
        if (start && !started) begin
            started <= 1;
            done <= 0;
        end else if (started) begin
            res <= {8'b0, and_bits};
            done <= 1;
            started <= 0;
        end else begin
            done <= 0;
        end
    end
endmodule