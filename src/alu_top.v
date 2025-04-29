`timescale 1ns/1ps

module alu_top (
    input clk,
    input reset,
    input start,
    input [2:0] op,           // operation selector
    input signed [7:0] in_a,
    input signed [7:0] in_b,
    output signed [15:0] result,
    output done
);

    wire load_a, load_b, load_out;
    wire start_mul, start_div, start_add, start_sub, start_and, start_or, start_xor;
    wire add_done, sub_done, and_done, or_done, xor_done, mul_done, div_done;
    wire [2:0] sel_op;

    wire [7:0] a_reg_out, b_reg_out;
    wire [15:0] alu_result_add, alu_result_sub, alu_result_and, alu_result_or, alu_result_xor;
    wire [15:0] alu_result_mul, alu_result_div;

    wire op_done;
    assign op_done = (op == 3'b000) ? add_done :
                     (op == 3'b001) ? sub_done :
                     (op == 3'b010) ? mul_done :
                     (op == 3'b011) ? div_done :
                     (op == 3'b100) ? and_done :
                     (op == 3'b101) ? or_done :
                     (op == 3'b110) ? xor_done : 1'b0;

    
    // === Control Unit ===
    alu_control ctrl (
        .clk(clk),
        .reset(reset),
        .start(start),
        .opcode(op),
        .op_done(op_done),  // << new
        .done(done),
        .load_a(load_a),
        .load_b(load_b),
        .load_out(load_out),
        .start_add(start_add),
        .start_sub(start_sub),
        .start_mul(start_mul),
        .start_div(start_div),
        .start_and(start_and),
        .start_or(start_or),
        .start_xor(start_xor),
        .sel_op(sel_op)
    );


    // === Input Registers ===
    regn #(8) reg_a (.clk(clk), .en(load_a), .d(in_a), .q(a_reg_out));
    regn #(8) reg_b (.clk(clk), .en(load_b), .d(in_b), .q(b_reg_out));

    // === Arithmetic Modules (dummy) ===
    
    alu_add add_unit (.clk(clk), .a(a_reg_out), .b(b_reg_out), .start(start_add), .sum(alu_result_add), .done(add_done));
    alu_sub sub_unit (.clk(clk), .a(a_reg_out), .b(b_reg_out), .start(start_sub), .diff(alu_result_sub), .done(sub_done));
    alu_and and_unit (.clk(clk), .a(a_reg_out), .b(b_reg_out), .start(start_and), .res(alu_result_and), .done(and_done));
    alu_or  or_unit  (.clk(clk), .a(a_reg_out), .b(b_reg_out), .start(start_or),  .res(alu_result_or), .done(or_done));
    alu_xor xor_unit (.clk(clk), .a(a_reg_out), .b(b_reg_out), .start(start_xor), .res(alu_result_xor), .done(xor_done));


    alu_mul mul_unit (.clk(clk), .reset(reset), .start(start_mul), .a(a_reg_out), .b(b_reg_out), .product(alu_result_mul), .done(mul_done));
    alu_div div_unit (.clk(clk), .reset(reset), .start(start_div), .a(a_reg_out), .b(b_reg_out), .quotient(alu_result_div), .done(div_done));

    // === Result MUX ===
    reg [15:0] result_mux;
    always @(*) begin
        case (sel_op)
            3'b000: result_mux = alu_result_add;
            3'b001: result_mux = alu_result_sub;
            3'b010: result_mux = alu_result_mul;
            3'b011: result_mux = alu_result_div;
            3'b100: result_mux = alu_result_and;
            3'b101: result_mux = alu_result_or;
            3'b110: result_mux = alu_result_xor;
            default: result_mux = 16'h0000;
        endcase
    end

    // === Output Register ===
    regn #(16) reg_out (.clk(clk), .en(load_out), .d(result_mux), .q(result));

endmodule
