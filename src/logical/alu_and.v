`timescale 1ns/1ps

module alu_and(
    input clk, 
    input [7:0] a, b, 
    input start, 
    output reg [15:0] res
);
    wire [7:0] and_bits;

    // Structural AND gates for each bit
    genvar i;
    generate
        for (i = 0; i < 8; i = i + 1) begin : and_loop
            and u_and(and_bits[i], a[i], b[i]);
        end
    endgenerate

    always @(posedge clk) begin
        if (start)
            res <= {8'b0, and_bits};  // zero-extend to 16 bits
    end
endmodule