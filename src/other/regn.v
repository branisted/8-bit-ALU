`timescale 1ns/1ps

module regn #(parameter N = 8) (
    input clk,
    input en,
    input [N-1:0] d,
    output reg [N-1:0] q
);
    always @(posedge clk)
        if (en)
            q <= d;
endmodule