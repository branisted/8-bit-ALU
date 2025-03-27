`timescale 1ns / 1ps

module multiplier #(
    parameter width = 8, // width of the input numbers
    parameter N = width / 2 // number of partial products
)(
    input [width-1:0] A,    // Multiplicand (M)
    input [width-1:0] B,    // Multiplier (Q)
    output [2*width-1:0] Product  // Product (P)
);

    // Internal signals
    reg [2:0] cc [0:N-1];   // Ck values
    reg [width:0] pp [0:N-1]; // Partial products
    reg signed [2*width-1:0] spp [0:N-1]; // Sign-extended partial products
    reg signed [2*width-1:0] prod; // Final product
    wire signed [width:0] inv_A; // Two's complement of multiplicand (A)

    // Generate two's complement of A
    assign inv_A = ~A + 1; // Two's complement of A

    integer kk, ii; // Declare loop variables

    always @ (A or B or inv_A) begin
        // Generate Ck for k = 0 (special case)
        cc[0] = {B[1], B[0], 1'b0}; // Ck for k=0
        
        // Generate Ck for other k values
        for (kk = 1; kk < N; kk = kk + 1) begin
            cc[kk] = {B[2*kk+1], B[2*kk], B[2*kk-1]}; // Ck for k>0
        end

        // Generate partial products based on Ck values
        for (kk = 0; kk < N; kk = kk + 1) begin
            case(cc[kk])
                3'b001, 3'b010: pp[kk] = {A[width-1], A}; // M (A)
                3'b011: pp[kk] = {A, 1'b0}; // 2M (2 * A)
                3'b100: pp[kk] = {inv_A[width-1:0], 1'b0}; // -M (-A)
                3'b101, 3'b110: pp[kk] = inv_A; // -2M (-2 * A)
                default: pp[kk] = 0; // 0
            endcase

            // Sign-extend the partial products
            spp[kk] = $signed(pp[kk]);

            // Shift each partial product according to its position (multiply by 2^k)
            for (ii = 0; ii < kk; ii = ii + 1) begin
                spp[kk] = {spp[kk], 2'b00}; // Shift by two (multiply by 2)
            end
        end

        // Sum the partial products to get the final product
        prod = spp[0];
        for (kk = 1; kk < N; kk = kk + 1) begin
            prod = prod + spp[kk];
        end
    end

    // Output the final product
    assign Product = prod;

endmodule
