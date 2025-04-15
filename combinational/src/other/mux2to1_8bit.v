module mux2x1_8bit(
    output wire [7:0] Y,
    input wire [7:0] A,   // First 8-bit input
    input wire [7:0] B,   // Second 8-bit input
    input wire Sel        // Select signal
);
    wire not_sel;
    wire [7:0] and_A, and_B;

    not (not_sel, Sel);  // not_sel = ~Sel

    genvar i;

    generate
        for (i = 0; i < 8; i = i + 1) begin
            and (and_A[i], A[i], not_sel);  // and_A[i] = A[i] & ~Sel
            and (and_B[i], B[i], Sel);      // and_B[i] = B[i] & Sel
            or  (Y[i], and_A[i], and_B[i]); // Y[i] = (A[i] & ~Sel) | (B[i] & Sel)
        end
    endgenerate

endmodule