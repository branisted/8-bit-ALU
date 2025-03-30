`timescale 1ns / 1ps

module alu_top (
    input wire clk,
    input wire rst,
    input wire start,
    input wire [1:0] opcode,      // 00: ADD/SUB, 01: MUL, 10: DIV
    input wire [7:0] operand_A,
    input wire [7:0] operand_B,
    output wire [15:0] result,
    output wire done
);

    wire load, compute, dec_count, reset_count;
    wire [1:0] select_op;
    wire zero_count;
    
    control_unit ctrl (
        .clk(clk),
        .rst(rst),
        .start(start),
        .opcode(opcode),
        .zero_count(zero_count),
        .load(load),
        .compute(compute),
        .dec_count(dec_count),
        .reset_count(reset_count),
        .done(done),
        .select_op(select_op)
    );

    wire [7:0] add_sub_result;
    wire add_sub_cout;

    wire [15:0] mul_result;
    wire [15:0] div_result;

    // Carry Lookahead Adder (CLA) for Addition
    adder cla_adder (
        .A(operand_A),
        .B(operand_B),
        .Cin(1'b0),
        .Sum(add_sub_result),
        .Cout(add_sub_cout)
    );

    // CLA-based Subtractor
    subtractor cla_subtractor (
        .A(operand_A),
        .B(operand_B),
        .Diff(add_sub_result),
        .Borrow(add_sub_cout)  // Borrow output
    );

    // Booth Multiplier
    multiplier booth_mul (
        .clk(clk),
        .rst(rst),
        .start(load),
        .multiplicand(operand_A),
        .multiplier(operand_B),
        .product(mul_result),
        .done(zero_count)
    );

    /*
    // Non-Restoring Divider (to be implemented similarly)
    divider nonrestoring_div (
        .clk(clk),
        .rst(rst),
        .start(load),
        .dividend(operand_A),
        .divisor(operand_B),
        .quotient(div_result),
        .done(zero_count)
    );
    */

    // MUX to select the correct result
    assign result = (select_op == 2'b00) ? {8'b0, add_sub_result} :  // Addition
                    (select_op == 2'b01) ? {8'b0, add_sub_result} :  // Subtraction
                    (select_op == 2'b10) ? mul_result :
                    div_result;
endmodule
