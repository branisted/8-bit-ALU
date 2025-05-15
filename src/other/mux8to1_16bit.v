`timescale 1ns/1ps

module mux8to1_16bit(
    input  wire [15:0] in0,
    input  wire [15:0] in1,
    input  wire [15:0] in2,
    input  wire [15:0] in3,
    input  wire [15:0] in4,
    input  wire [15:0] in5,
    input  wire [15:0] in6,
    input  wire [15:0] in7,
    input  wire [2:0] sel,
    output wire [15:0] y
);
    genvar i;
    generate
        for (i = 0; i < 16; i = i + 1) begin : mux_bit
            mux8to1 mux_inst (
                .in({in7[i], in6[i], in5[i], in4[i], in3[i], in2[i], in1[i], in0[i]}),
                .sel(sel),
                .y(y[i])
            );
        end
    endgenerate
endmodule
