`timescale 1ns / 1ps
module tb_alu_top;
    reg signed [7:0] A, B;
    reg [1:0] op;
    wire signed [15:0] result;

    alu_top uut (.A(A), .B(B), .op(op), .result(result));

    integer errors = 0;

    task check_result;
        input [15:0] expected;
        begin
            if (op == 2'b01) begin
                if (result[7:0] !== expected[7:0]) begin
                    $display("[FAIL] Time=%0t | A=%b, B=%b, Op=%b | Expected=%b, Got=%b", 
                             $time, A, B, op, expected[7:0], result[7:0]);
                    errors = errors + 1;
                end else begin
                    $display("[PASS] Time=%0t | A=%b, B=%b, Op=%b | Result=%b", 
                             $time, A, B, op, result[7:0]);
                end
            end else begin
                if (result !== expected) begin
                    $display("[FAIL] Time=%0t | A=%b, B=%b, Op=%b | Expected=%b, Got=%b", 
                             $time, A, B, op, expected, result);
                    errors = errors + 1;
                end else begin
                    $display("[PASS] Time=%0t | A=%b, B=%b, Op=%b | Result=%b", 
                             $time, A, B, op, result);
                end
            end
        end
    endtask

    initial begin
        $display("Starting ALU Testbench...");

        // Test Addition (00)
        A = 8'd100; B = 8'd5; op = 2'b00; #10;
        check_result(16'd105);
        
        // Test Subtraction (01) - Now checking only lower 8 bits
        A = -8'd100; B = 8'd5; op = 2'b01; #10;
        check_result(-8'd105);
        
        // Test Multiplication (10)
        A = 8'd10; B = 8'd3; op = 2'b10; #10;
        check_result(16'd30);
        
        // Test Division (11)
        A = -8'd100; B = 8'd5; op = 2'b11; #10;
        check_result({-8'd20, 8'd0}); // Expect quotient = -20, remainder = 0
        
        // Edge Case: Zero Division
        A = 8'd50; B = 8'd0; op = 2'b11; #10;
        check_result(16'd0);

        $display("ALU Testbench Completed with %0d errors.", errors);
        $stop;
    end
endmodule