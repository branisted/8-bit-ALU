module twos_complement(output [7:0] out, input [7:0] in);
    wire [7:0] not_in;  // Inverted input
    wire [7:0] carry;   // Carry propagation for addition

    // Step 1: Invert each bit (1's complement)
    genvar i;
    generate
        for (i = 0; i < 8; i = i + 1) begin
            not (not_in[i], in[i]); 
        end
    endgenerate

    // Step 2: Add 1 using full adders
    full_adder FA0 (not_in[0], 1'b1, 1'b0, out[0], carry[0]); // Add 1 to LSB
    generate
        for (i = 1; i < 8; i = i + 1) begin
            full_adder FA0 (not_in[i], 1'b0, carry[i-1], out[i], carry[i]); // Propagate carry
        end
    endgenerate
endmodule