`timescale 1ns / 1ps

module tb_control_unit;

    // Declare testbench signals
    reg [1:0] op_sel;    // Operation selector (input)
    reg clk;              // Clock signal (input)
    reg reset;            // Reset signal (input)
    wire load_alu;        // Load ALU signal (output)
    wire [1:0] alu_op;    // ALU operation selector (output)
    wire done;            // Completion signal (output)

    // Instantiate the control_unit
    control_unit uut (
        .op_sel(op_sel),
        .clk(clk),
        .reset(reset),
        .load_alu(load_alu),
        .alu_op(alu_op),
        .done(done)
    );

    // Generate clock signal (period of 10ns)
    always begin
        #5 clk = ~clk;
    end

    // Test sequence
    initial begin
        // Initialize signals
        clk = 0;
        reset = 0;
        op_sel = 2'b00;  // Default operation (ADD)

        // Apply reset
        $display("Applying reset...");
        reset = 1;
        #10;
        reset = 0;
        #10;

        // Test ADD operation (op_sel = 00)
        op_sel = 2'b00;
        $display("Test: op_sel = 00 (ADD)");
        #10;

        // Test SUB operation (op_sel = 01)
        op_sel = 2'b01;
        $display("Test: op_sel = 01 (SUB)");
        #10;

        // Test MUL operation (op_sel = 10)
        op_sel = 2'b10;
        $display("Test: op_sel = 10 (MUL)");
        #10;

        // Test DIV operation (op_sel = 11)
        op_sel = 2'b11;
        $display("Test: op_sel = 11 (DIV)");
        #10;

        // Test with reset again
        $display("Applying reset again...");
        reset = 1;
        #10;
        reset = 0;
        #10;

        // Finish simulation
        $finish;
    end

    // Monitor changes
    initial begin
        $monitor("At time %t: op_sel = %b, load_alu = %b, alu_op = %b, done = %b", 
                  $time, op_sel, load_alu, alu_op, done);
    end

endmodule
