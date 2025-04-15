`timescale 1ns / 1ps

module tb_adder;
    // Testbench Signals
    reg [7:0] A, B;
    reg Cin;
    wire [7:0] Sum;
    wire Cout;

    // Instantiate the 8-bit CLA
    adder uut (
        .A(A),
        .B(B),
        .Cin(Cin),
        .Sum(Sum),
        .Cout(Cout)
    );

    // Helper Task: Check and Print Results
    task check_result;
        input [7:0] expected_sum;
        input expected_cout;
        begin
            if (Sum !== expected_sum || Cout !== expected_cout) begin
                $display("TEST FAILED: A=%b, B=%b, Cin=%b | Expected: Sum=%b, Cout=%b | Got: Sum=%b, Cout=%b", 
                         A, B, Cin, expected_sum, expected_cout, Sum, Cout);
            end else begin
                $display("TEST PASSED: A=%b, B=%b, Cin=%b | Sum=%b, Cout=%b", 
                         A, B, Cin, Sum, Cout);
            end
        end
    endtask

    // Simulation Process
    initial begin
        
        $display("Starting 8-bit CLA Testbench...");
        
        // Test Case 1: Zero Inputs
        A = 8'b00000000; B = 8'b00000000; Cin = 1'b0;
        #10 check_result(8'b00000000, 1'b0);
        
        // Test Case 2: Adding 1 to Zero
        A = 8'b00000001; B = 8'b00000000; Cin = 1'b0;
        #10 check_result(8'b00000001, 1'b0);

        // Test Case 3: Maximum Unsigned Addition (255 + 255)
        A = 8'b11111111; B = 8'b11111111; Cin = 1'b0;
        #10 check_result(8'b11111110, 1'b1);

        // Test Case 4: Maximum Unsigned Addition with Carry-in
        A = 8'b11111111; B = 8'b11111111; Cin = 1'b1;
        #10 check_result(8'b11111111, 1'b1);

        // Test Case 5: Random Value 1
        A = 8'b10101010; B = 8'b01010101; Cin = 1'b0;
        #10 check_result(8'b11111111, 1'b0);

        // Test Case 6: Random Value 2
        A = 8'b11001100; B = 8'b00110011; Cin = 1'b1;
        #10 check_result(8'b00000000, 1'b1);

        // Test Case 7: Overflow Detection
        A = 8'b10000000; B = 8'b10000000; Cin = 1'b0;
        #10 check_result(8'b00000000, 1'b1);

        // Test Case 8: Carry-in Propagation
        A = 8'b00000000; B = 8'b00000000; Cin = 1'b1;
        #10 check_result(8'b00000001, 1'b0);

        // Test Case 9: Edge Case - Alternating Bits
        A = 8'b01010101; B = 8'b10101010; Cin = 1'b1;
        #10 check_result(8'b00000000, 1'b1);

        // Test Case 10: Random Large Values
        A = 8'b11110000; B = 8'b00001111; Cin = 1'b0;
        #10 check_result(8'b11111111, 1'b0);

        // Test Case 11: Random Small Values
        A = 8'b00001111; B = 8'b00000001; Cin = 1'b1;
        #10 check_result(8'b00010001, 1'b0);

        // Test Case 12: Random Middle Values
        A = 8'b01101011; B = 8'b00100101; Cin = 1'b0;
        #10 check_result(8'b10010000, 1'b0);

        $display("All tests completed.");
        $finish;
    end
endmodule
