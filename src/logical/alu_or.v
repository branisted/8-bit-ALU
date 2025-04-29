`timescale 1ns/1ps
// ALU OR
module alu_or (
    input clk,
    input [7:0] a, b,
    input start,
    output reg [15:0] res,
    output reg done
);
    reg started = 0;
    wire [7:0] or_bits = a | b;

    always @(posedge clk) begin
        if (start && !started) begin
            started <= 1;
            done <= 0;
        end else if (started) begin
            res <= {8'b0, or_bits};
            done <= 1;
            started <= 0;
        end else begin
            done <= 0;
        end
    end
endmodule