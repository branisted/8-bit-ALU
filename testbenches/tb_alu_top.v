`timescale 1ns / 1ps

// File: alu_top_tb.v
module tb_alu_top;
    // Testbench signals
    reg clk, rst, start;
    reg [1:0] opcode;   // 00: ADD, 01: SUB, 10: MUL
    reg [7:0] operand_A, operand_B;
    wire [15:0] result;
    wire done;

    // Instantiate the ALU
    alu_top uut (
        .clk(clk),
        .rst(rst),
        .start(start),
        .opcode(opcode),
        .operand_A(operand_A),
        .operand_B(operand_B),
        .result(result),
        .done(done)
    );

    // Clock Generation (10ns period)
    always #5 clk = ~clk; 

    // Test Procedure
    initial begin
        // Initialize signals
        clk = 0;
        rst = 1;
        start = 0;
        opcode = 2'b00;
        operand_A = 0;
        operand_B = 0;

        #10 rst = 0; // Release reset

        // Test Case 1: Addition (15 + 10)
        #10 operand_A = 8'd15;
            operand_B = 8'd10;
            opcode = 2'b00; // ADD
            start = 1;
        #10 start = 0;
        #10 $display("ADD: %d + %d = %d", operand_A, operand_B, result);

        // Test Case 2: Subtraction (20 - 5)
        #20 operand_A = 8'd20;
            operand_B = 8'd5;
            opcode = 2'b01; // SUB
            start = 1;
        #10 start = 0;
        #10 $display("SUB: %d - %d = %d", operand_A, operand_B, result);

        // Test Case 3: Multiplication (7 * 3)
        #20 operand_A = 8'd7;
            operand_B = 8'd3;
            opcode = 2'b10; // MUL
            start = 1;
        #10 start = 0;
        wait(done);
        #10 $display("MUL: %d * %d = %d", operand_A, operand_B, result);

        /*
        // Test Case 4: Division (A = 40, B = 5)
        #20 operand_A = 8'd40;
            operand_B = 8'd5;
            opcode = 2'b11; // DIV
            start = 1;
        #10 start = 0;
        wait(done);
        #10 $display("DIV: %d / %d = %d", operand_A, operand_B, result);
        */

        // End simulation
        #20 $finish;
    end
endmodule