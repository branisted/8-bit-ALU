`timescale 1ns/1ps

module alu_div(
    input clk,
    input start,
    input signed [7:0] a, b,
    output reg signed [15:0] quotient,
    output reg done
);
    always @(posedge clk) begin
        if (start) begin
            quotient <= (b != 0) ? a / b : 8'hFF; // handle div-by-zero
            done <= 1;
        end else begin
            done <= 0;
        end
    end
endmodule