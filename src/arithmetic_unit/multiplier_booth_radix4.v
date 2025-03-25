module booth_encoder (
    input [1:0] b, // Two bits of the multiplier
    input [7:0] A, // Multiplicand
    output reg [8:0] PP // 9-bit Partial Product (including sign bit)
);
    always @(*) begin
        case (b)
            2'b00: PP = 9'b000000000;   // 0 * A
            2'b01: PP = {A[7], A};      // +A
            2'b10: PP = ~{A[7], A} + 1; // -A (2’s complement)
            2'b11: PP = ~( {A[7], A} << 1 ) + 1; // -2A (2’s complement)
            default: PP = 9'b000000000;
        endcase
    end
endmodule


module cla_9bit (
    input [8:0] A, B,
    input Cin,
    output [8:0] Sum,
    output Cout
);
    wire [8:0] P, G;
    wire [8:0] C;

    assign P = A ^ B; // Propagate
    assign G = A & B; // Generate

    assign C[0] = Cin;
    assign C[1] = G[0] | (P[0] & C[0]);
    assign C[2] = G[1] | (P[1] & C[1]);
    assign C[3] = G[2] | (P[2] & C[2]);
    assign C[4] = G[3] | (P[3] & C[3]);
    assign C[5] = G[4] | (P[4] & C[4]);
    assign C[6] = G[5] | (P[5] & C[5]);
    assign C[7] = G[6] | (P[6] & C[6]);
    assign C[8] = G[7] | (P[7] & C[7]);

    assign Sum = P ^ C;
    assign Cout = G[8] | (P[8] & C[8]);

endmodule

module multiplier_booth_radix4 (
    input [7:0] A, B,
    output [15:0] Product
);
    wire [8:0] PP0, PP1, PP2, PP3; // Partial products
    wire [15:0] shifted_PP0, shifted_PP1, shifted_PP2, shifted_PP3;
    wire [15:0] sum1, sum2, final_sum;

    // Booth Encoders
    booth_encoder BE0 (.b(B[1:0]), .A(A), .PP(PP0));
    booth_encoder BE1 (.b(B[3:2]), .A(A), .PP(PP1));
    booth_encoder BE2 (.b(B[5:4]), .A(A), .PP(PP2));
    booth_encoder BE3 (.b(B[7:6]), .A(A), .PP(PP3));

    // Shift Partial Products
    assign shifted_PP0 = {PP0, 6'b000000}; // No shift
    assign shifted_PP1 = {PP1, 4'b0000, 2'b00}; // Shift left 2
    assign shifted_PP2 = {PP2, 2'b00, 4'b0000}; // Shift left 4
    assign shifted_PP3 = {PP3, 6'b000000}; // Shift left 6

    // First level of addition
    cla_9bit ADD1 (.A(shifted_PP0[8:0]), .B(shifted_PP1[8:0]), .Cin(1'b0), .Sum(sum1[8:0]));
    cla_9bit ADD2 (.A(shifted_PP2[8:0]), .B(shifted_PP3[8:0]), .Cin(1'b0), .Sum(sum2[8:0]));

    // Final summation
    cla_9bit ADD3 (.A(sum1[8:0]), .B(sum2[8:0]), .Cin(1'b0), .Sum(final_sum[8:0]));

    assign Product = {final_sum, 8'b00000000}; // Extend final sum

endmodule