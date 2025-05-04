`timescale 1ns/1ps

module ones_complement(
    input [7:0] a,
    output [7:0] not_a
);
    genvar i;
    generate
        for (i = 0; i < 8; i = i + 1) begin : gen_complement
            not (not_a[i], a[i]);
        end
    endgenerate

endmodule