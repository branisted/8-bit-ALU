`timescale 1ns / 1ps

module tb_multiplier;
    // Testbench Signals
    reg signed [7:0] A, B;
    wire signed [15:0] result;

    // Instantiate the multiplier
    multiplier uut (
        .A(A),
        .B(B),
        .result(result)
    );

    // Helper Task: Check and Print Results
    task check_result;
        input signed [15:0] expected_result;
        begin
            if (result !== expected_result) begin
                $display("TEST FAILED: A=%d (%b), B=%d (%b) | Expected: result=%d (%b) | Got: result=%d (%b)", 
                         A, A, B, B, expected_result, expected_result, result, result);
            end else begin
                $display("TEST PASSED: A=%d (%b), B=%d (%b) | result=%d (%b)", 
                         A, A, B, B, result, result);
            end
        end
    endtask

    // Simulation Process
    initial begin
        $display("Starting Booth Radix-4 Multiplier Testbench...");

        // Test Case 1: Zero Inputs
        A = 8'd0; B = 8'd0;
        #10 check_result(16'd0);

        // Test Case 2: Positive Small Numbers
        A = 8'd5; B = 8'd6;
        #10 check_result(16'd30);

        // Test Case 3: Maximum Positive Values
        A = 8'd127; B = 8'd127;
        #10 check_result(16'd16129);  // 127 * 127

        // Test Case 4: Minimum Negative Values
        A = -8'd128; B = -8'd128;
        #10 check_result(16'd16384);  // -128 * -128

        // Test Case 5: Positive × Negative
        A = 8'd100; B = -8'd6;
        #10 check_result(-16'd600);

        // Test Case 6: Negative × Positive
        A = -8'd15; B = 8'd20;
        #10 check_result(-16'd300);

        // Test Case 7: Edge Case - Max Positive × Min Negative
        A = 8'd127; B = -8'd128;
        #10 check_result(-16'd16256);

        // Test Case 8: Small Negative Numbers
        A = -8'd3; B = -8'd4;
        #10 check_result(16'd12);

        // Test Case 9: Random Value 1 (corrected)
        A = -8'd86; B = 8'd85;  // -86 × 85
        #10 check_result(-16'd7310);

        // Test Case 10: Random Value 2
        A = -8'd45; B = 8'd73;
        #10 check_result(-16'd3285);

        // Test Case 11: Power of 2 Multiplication
        A = 8'd16; B = 8'd8;  // 16 * 8
        #10 check_result(16'd128);

        // Test Case 12: Zero × Negative
        A = 8'd0; B = -8'd100;
        #10 check_result(16'd0);

        // Test Case 13: Large Positive × Negative (corrected)
        A = 8'd100; B = -8'd6;
        #10 check_result(-16'd600);

        // Test Case 14: Alternating Bits (corrected)
        A = 8'd85; B = -8'd86;  // 85 × -86
        #10 check_result(-16'd7310);

        // Test Case 15: Edge Case - Positive × Negative One (corrected)
        A = 8'd64; B = -8'd1;
        #10 check_result(-16'd64);

        // Test Case 16: Random Middle Values
        A = 8'd73; B = -8'd19;
        #10 check_result(-16'd1387);

        $display("All tests completed.");
        $finish;
    end
endmodule