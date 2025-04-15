module booth_encoder(input [2:0] triplet, output reg [2:0] sel);
    always @(*) begin
        case (triplet)
            3'b000, 3'b111: sel = 3'b000; // Zero
            3'b001, 3'b010: sel = 3'b001; // +A
            3'b011: sel = 3'b010;         // +2A
            3'b100: sel = 3'b110;         // -2A
            3'b101, 3'b110: sel = 3'b101; // -A
            default: sel = 3'b000;
        endcase
    end
endmodule

module partial_product(input signed [7:0] A, input [2:0] sel, output signed [15:0] pp);
    wire signed [15:0] pp_plusA  = { {8{A[7]}}, A };       // Sign-extended +A
    wire signed [15:0] pp_plus2A = { {7{A[7]}}, A, 1'b0 }; // Sign-extended +2A
    wire signed [15:0] pp_negA   = -pp_plusA;             // -A
    wire signed [15:0] pp_neg2A  = -pp_plus2A;            // -2A
    
    assign pp = (sel == 3'b001) ? pp_plusA  :
                (sel == 3'b010) ? pp_plus2A :
                (sel == 3'b101) ? pp_negA   :
                (sel == 3'b110) ? pp_neg2A  :
                16'b0;
endmodule

module full_adder(input a, b, cin, output sum, cout);
    assign sum = a ^ b ^ cin;
    assign cout = (a & b) | (b & cin) | (a & cin);
endmodule

module adder_16bit(input signed [15:0] a, b, output signed [15:0] sum, output cout);
    wire [15:0] carry;
    
    full_adder fa0(a[0], b[0], 1'b0, sum[0], carry[0]);
    full_adder fa1(a[1], b[1], carry[0], sum[1], carry[1]);
    full_adder fa2(a[2], b[2], carry[1], sum[2], carry[2]);
    full_adder fa3(a[3], b[3], carry[2], sum[3], carry[3]);
    full_adder fa4(a[4], b[4], carry[3], sum[4], carry[4]);
    full_adder fa5(a[5], b[5], carry[4], sum[5], carry[5]);
    full_adder fa6(a[6], b[6], carry[5], sum[6], carry[6]);
    full_adder fa7(a[7], b[7], carry[6], sum[7], carry[7]);
    full_adder fa8(a[8], b[8], carry[7], sum[8], carry[8]);
    full_adder fa9(a[9], b[9], carry[8], sum[9], carry[9]);
    full_adder fa10(a[10], b[10], carry[9], sum[10], carry[10]);
    full_adder fa11(a[11], b[11], carry[10], sum[11], carry[11]);
    full_adder fa12(a[12], b[12], carry[11], sum[12], carry[12]);
    full_adder fa13(a[13], b[13], carry[12], sum[13], carry[13]);
    full_adder fa14(a[14], b[14], carry[13], sum[14], carry[14]);
    full_adder fa15(a[15], b[15], carry[14], sum[15], cout);
endmodule

module multiplier(input signed [7:0] A, B, output signed [15:0] result);
    wire [2:0] sel0, sel1, sel2, sel3;
    wire signed [15:0] pp0, pp1, pp2, pp3;
    wire signed [15:0] sum0, sum1, sum2;
    wire cout0, cout1, cout2;

    // Booth encoding
    booth_encoder enc0(.triplet({B[1:0], 1'b0}), .sel(sel0));
    booth_encoder enc1(.triplet(B[3:1]), .sel(sel1));
    booth_encoder enc2(.triplet(B[5:3]), .sel(sel2));
    booth_encoder enc3(.triplet(B[7:5]), .sel(sel3));

    // Generate partial products
    partial_product pp_gen0(.A(A), .sel(sel0), .pp(pp0));
    partial_product pp_gen1(.A(A), .sel(sel1), .pp(pp1));
    partial_product pp_gen2(.A(A), .sel(sel2), .pp(pp2));
    partial_product pp_gen3(.A(A), .sel(sel3), .pp(pp3));

    // Proper sign extension and shifting
    wire signed [17:0] pp0_ext = { {2{pp0[15]}}, pp0 };
    wire signed [17:0] pp1_ext = { {2{pp1[15]}}, pp1 } << 2;
    wire signed [17:0] pp2_ext = { {2{pp2[15]}}, pp2 } << 4;
    wire signed [17:0] pp3_ext = { {2{pp3[15]}}, pp3 } << 6;

    // Addition stages
    wire signed [17:0] sum0_ext;
    wire signed [17:0] sum1_ext;
    
    adder_16bit add0(.a(pp0_ext[15:0]), .b(pp1_ext[15:0]), .sum(sum0_ext[15:0]), .cout(cout0));
    adder_16bit add1(.a(sum0_ext[15:0]), .b(pp2_ext[15:0]), .sum(sum1_ext[15:0]), .cout(cout1));
    adder_16bit add2(.a(sum1_ext[15:0]), .b(pp3_ext[15:0]), .sum(result), .cout(cout2));

endmodule