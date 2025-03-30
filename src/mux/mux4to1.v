`timescale 1ns / 1ps

module mux2to1 (
    input wire A,      // First input
    input wire B,      // Second input
    input wire sel,    // Selector
    output wire out    // Output
);
    assign out = (sel) ? B : A;  // If sel is 1, output B; if sel is 0, output A
endmodule

module mux4to1 (
    input wire [15:0] data,  // 16-bit input (data[15:0])
    input wire [1:0] sel,    // 2-bit selector (sel[1], sel[0])
    output wire [15:0] out   // 16-bit output
);
    wire [15:0] mux0_out, mux1_out;  // Intermediate signals for 2-to-1 muxes

    // First level of muxes (2-to-1)
    genvar i; // Generate variable for bit-level operations
    generate
        for (i = 0; i < 16; i = i + 1) begin : mux_level_0
            mux2to1 mux0 (
                .A(data[i]),
                .B(data[i + 1]),
                .sel(sel[0]),
                .out(mux0_out[i])
            );
        end
    endgenerate

    // Second level mux (2-to-1) to select between the outputs of mux0 and mux1
    generate
        for (i = 0; i < 16; i = i + 1) begin : mux_level_1
            mux2to1 mux1 (
                .A(mux0_out[i]),
                .B(mux0_out[i + 1]),
                .sel(sel[1]),
                .out(out[i])
            );
        end
    endgenerate

endmodule