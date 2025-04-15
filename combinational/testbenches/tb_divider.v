`timescale 1ns / 1ps

module tb_divider;
    // Testbench Signals
    reg signed [7:0] dividend, divisor;
    wire signed [7:0] quotient, remainder;

    // Instantiate the Non-Restoring Divider
    divider uut (
        .dividend(dividend),
        .divisor(divisor),
        .quotient(quotient),
        .remainder(remainder)
    );

    // Helper Task: Check and Print Results
    task check_result;
        input signed [7:0] expected_quotient;
        input signed [7:0] expected_remainder;
        begin
            if (quotient !== expected_quotient || remainder !== expected_remainder) begin
                $display("TEST FAILED: dividend=%d, divisor=%d | Expected: quotient=%d, remainder=%d | Got: quotient=%d, remainder=%d", 
                         dividend, divisor, expected_quotient, expected_remainder, quotient, remainder);
            end else begin
                $display("TEST PASSED: dividend=%d, divisor=%d | quotient=%d, remainder=%d", 
                         dividend, divisor, quotient, remainder);
            end
        end
    endtask

    // Simulation Process
    initial begin
        $display("Starting Non-Restoring Division Testbench...");
        
        // Test Case 1: 16 / 4 = 4 R0
        dividend = 8'd16; divisor = 8'd4;
        #10 check_result(8'd4, 8'd0);
        
        // Test Case 2: -16 / 4 = -4 R0
        dividend = -8'd16; divisor = 8'd4;
        #10 check_result(-8'd4, 8'd0);
        
        // Test Case 3: 19 / 4 = 4 R3
        dividend = 8'd19; divisor = 8'd4;
        #10 check_result(8'd4, 8'd3);
        
        // Test Case 4: -19 / 4 = -4 R-3
        dividend = -8'd19; divisor = 8'd4;
        #10 check_result(-8'd4, -8'd3);
        
        // Test Case 5: 127 / 5 = 25 R2
        dividend = 8'd127; divisor = 8'd5;
        #10 check_result(8'd25, 8'd2);
        
        // Test Case 6: -127 / 5 = -25 R-2
        dividend = -8'd127; divisor = 8'd5;
        #10 check_result(-8'd25, -8'd2);
        
        // Test Case 7: Edge Case - Division by Zero
        dividend = 8'd50; divisor = 8'd0;
        #10 check_result(8'd0, 8'd0);
        
        // Test Case 8: Edge Case - Division by -1
        dividend = -8'd100; divisor = -8'd1;
        #10 check_result(8'd100, 8'd0);
        
        // Test Case 9: Smallest Negative Number divided by -1 (Avoid Overflow)
        dividend = -8'd128; divisor = -8'd1;
        #10 check_result(8'd127, 8'd0);
        
        // Test Case 10: 100 / -7 = -14 R2
        dividend = 8'd100; divisor = -8'd7;
        #10 check_result(-8'd14, 8'd2);
        
        $display("All tests completed.");
        $finish;
    end
endmodule