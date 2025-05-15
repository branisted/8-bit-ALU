`timescale 1ns/1ps

module alu_top (
    input clk,
    input reset,
    input start,
    input [2:0] op,
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

    // Selectarea semnalului done
    wire [7:0] done_signals;
    assign done_signals[0] = add_done;
    assign done_signals[1] = sub_done;
    assign done_signals[2] = mul_done;
    assign done_signals[3] = div_done;
    assign done_signals[4] = and_done;
    assign done_signals[5] = or_done;
    assign done_signals[6] = xor_done;
    assign done_signals[7] = 1'b0;

    mux8to1 op_done_mux (
        .in(done_signals),
        .sel(op),
        .y(op_done)
    );

    // Instantierea control unit-ului
    alu_control ctrl (
        .clk(clk),
        .reset(reset),
        .start(start),
        .opcode(op),
        .op_done(op_done),
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

    // Registri de input
    regn #(8) reg_a (.clk(clk), .en(load_a), .d(in_a), .q(a_reg_out));
    regn #(8) reg_b (.clk(clk), .en(load_b), .d(in_b), .q(b_reg_out));

    // Instantierea modulelor aritmetice
    alu_add add_unit (.clk(clk), .reset(reset), .a(a_reg_out), .b(b_reg_out), .start(start_add), .sum(alu_result_add), .done(add_done));
    alu_sub sub_unit (.clk(clk), .reset(reset), .a(a_reg_out), .b(b_reg_out), .start(start_sub), .diff(alu_result_sub), .done(sub_done));
    alu_and and_unit (.clk(clk), .reset(reset), .a(a_reg_out), .b(b_reg_out), .start(start_and), .res(alu_result_and), .done(and_done));
    alu_or  or_unit  (.clk(clk), .reset(reset), .a(a_reg_out), .b(b_reg_out), .start(start_or),  .res(alu_result_or), .done(or_done));
    alu_xor xor_unit (.clk(clk), .reset(reset), .a(a_reg_out), .b(b_reg_out), .start(start_xor), .res(alu_result_xor), .done(xor_done));
    alu_mul mul_unit (.clk(clk), .reset(reset), .start(start_mul), .a(a_reg_out), .b(b_reg_out), .product(alu_result_mul), .done(mul_done));
    alu_div div_unit (.clk(clk), .reset(reset), .start(start_div), .a(a_reg_out), .b(b_reg_out), .quotient(alu_result_div), .done(div_done));

    // Mux 8 to 1 16 bit 
    wire [15:0] result_mux;

    mux8to1_16bit result_mux_inst (
        .in0(alu_result_add),
        .in1(alu_result_sub),
        .in2(alu_result_mul),
        .in3(alu_result_div),
        .in4(alu_result_and),
        .in5(alu_result_or),
        .in6(alu_result_xor),
        .in7(16'h0000),
        .sel(sel_op),
        .y(result_mux)
    );

    // Registru de iesire
    regn #(16) reg_out (.clk(clk), .en(load_out), .d(result_mux), .q(result));

endmodule
