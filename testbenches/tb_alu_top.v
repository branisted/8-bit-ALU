`timescale 1ns / 1ps

module tb_alu_top();

    // Inputs
    reg clk = 0;
    reg rst = 1;
    reg start = 0;
    reg [2:0] alu_op = 3'b000;
    reg [7:0] operand_a = 8'h00;
    reg [7:0] operand_b = 8'h00;

    // Outputs
    wire done;
    wire [15:0] result;

    // Instantiate DUT
    alu_top DUT (
        .clk(clk),
        .reset(rst),
        .start(start),
        .op(alu_op),
        .in_a(operand_a),
        .in_b(operand_b),
        .done(done),
        .result(result)
    );

    // Clock
    always #5 clk = ~clk;

    // Display task
    task display_state(input [127:0] opname);
        $display("T=%0t | %-4s | A=%0d, B=%0d => Result=%0d | Done=%b", 
            $time, opname, operand_a, operand_b, result, done);
    endtask

    // Test Procedure
    initial begin
        $display("==== STARTING ALU TESTBENCH ====");

        // Initialize
        #20 rst = 0; // Release reset
        #20;

        // Test operations
        test_operation(3'b000, 25, 17, "ADD");
        test_operation(3'b001, 42, 15, "SUB");
        test_operation(3'b010, 6, 9, "MUL");
        test_operation(3'b011, 100, 4, "DIV");
        test_operation(3'b011, 10, 0, "DIV0");
        test_operation(3'b100, 8'b10101010, 8'b11001100, "AND");
        test_operation(3'b101, 8'b10101010, 8'b11001100, "OR");
        test_operation(3'b110, 8'b10101010, 8'b11001100, "XOR");

        $display("==== ALU TESTBENCH COMPLETE ====");
        $stop;
    end

    // Test operation task
    task test_operation(input [2:0] op, input signed [7:0] a, input signed [7:0] b, input [127:0] opname);
        begin
            // Setup operation
            @(negedge clk); // Synchronize with clock
            alu_op = op;
            operand_a = a;
            operand_b = b;
            start = 1;
            
            // Wait one cycle then clear start
            @(negedge clk);
            start = 0;
            
            // Wait for done signal (synchronized with clock)
            @(posedge done); // Wait for done to go high
            
            // Wait one more clock to ensure result is stable
            @(negedge clk);
            display_state(opname);
            
            // Wait a couple cycles between tests
            #20;
        end
    endtask

endmodule

/*
module tb_alu_top();

    // Inputs
    reg clk = 0;
    reg rst = 1;
    reg start = 0;
    reg [2:0] alu_op = 3'b000;
    reg [7:0] operand_a = 8'h00;
    reg [7:0] operand_b = 8'h00;

    // Outputs
    wire done;
    wire [15:0] result;

    // Instantiate DUT
    alu_top DUT (
        .clk(clk),
        .reset(rst),
        .start(start),
        .op(alu_op),
        .in_a(operand_a),
        .in_b(operand_b),
        .done(done),
        .result(result)
    );

    // Clock
    always #5 clk = ~clk;

    // Display task
    task display_state(input [127:0] opname);
        $display("T=%0t | %-4s | A=%0d, B=%0d => Result=%0d | Done=%b", 
            $time, opname, operand_a, operand_b, result, done);
    endtask

    // Test Procedure
    initial begin
        $display("==== STARTING ALU TESTBENCH ====");

        #20 rst = 0; // Release reset
        #20;

        // --- Test ADD ---
        alu_op = 3'b000; operand_a = 8'd25; operand_b = 8'd17; start = 1;
        #10 start = 0;
        #100 display_state("ADD");

        // --- Test SUB ---
        alu_op = 3'b001; operand_a = 8'd42; operand_b = 8'd15; start = 1;
        #10 start = 0;
        #100 display_state("SUB");

        // --- Test MUL ---
        alu_op = 3'b010; operand_a = 8'd6; operand_b = 8'd9; start = 1;
        #10 start = 0;
        #100 display_state("MUL");

        // --- Test DIV ---
        alu_op = 3'b011; operand_a = 8'd100; operand_b = 8'd4; start = 1;
        #10 start = 0;
        #100 display_state("DIV");

        // --- Test DIV by 0 ---
        alu_op = 3'b011; operand_a = 8'd10; operand_b = 8'd0; start = 1;
        #10 start = 0;
        #100 display_state("DIV0");

        // --- Test AND ---
        alu_op = 3'b100; operand_a = 8'b10101010; operand_b = 8'b11001100; start = 1;
        #10 start = 0;
        #100 display_state("AND");

        // --- Test OR ---
        alu_op = 3'b101; operand_a = 8'b10101010; operand_b = 8'b11001100; start = 1;
        #10 start = 0;
        #100 display_state("OR");

        // --- Test XOR ---
        alu_op = 3'b110; operand_a = 8'b10101010; operand_b = 8'b11001100; start = 1;
        #10 start = 0;
        #100 display_state("XOR");

        $display("==== ALU TESTBENCH COMPLETE ====");
        $stop;
    end

endmodule
*/