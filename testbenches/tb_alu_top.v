`timescale 1ns / 1ps

module tb_alu_top;

    // Declare signals for testing
    reg [7:0] A, B;
    reg [1:0] op_sel;
    reg clk, reset;
    wire [15:0] result;

    // Instantiate the alu_top module
    alu_top uut (
        .A(A),
        .B(B),
        .op_sel(op_sel),
        .clk(clk),
        .reset(reset),
        .result(result)
    );

    // Clock generation
    always begin
        #5 clk = ~clk;  // Clock with 10ns period (50 MHz)
    end

    // Stimulus process
    initial begin
        // Initialize signals
        clk = 0;
        reset = 1;
        A = 8'b0;
        B = 8'b0;
        op_sel = 2'b00;

        // Apply reset
        #10 reset = 0;

        // Test cases
        #10 A = 8'b10101010; B = 8'b01010101; op_sel = 2'b00; // ADD
        #20 A = 8'b10101010; B = 8'b01010101; op_sel = 2'b01; // SUB
        #20 A = 8'b00000011; B = 8'b00000010; op_sel = 2'b10; // MUL
        #20 A = 8'b00000100; B = 8'b00000010; op_sel = 2'b11; // DIV

        // Finish the simulation
        #20 $finish;
    end

    // Monitor and log relevant signals
    initial begin
        $monitor("Time = %t | A = %b | B = %b | op_sel = %b | result = %b", 
                 $time, A, B, op_sel, result);
    end

endmodule