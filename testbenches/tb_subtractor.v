`timescale 1ns/1ps

module tb_subtractor;
    reg [7:0] A, B;
    wire [7:0] Diff;
    wire Borrow;

    subtractor uut (
        .A(A),
        .B(B),
        .Diff(Diff),
        .Borrow(Borrow)
    );

    task check_result;
        input [7:0] expected_diff;
        input expected_borrow;
        begin
            if (Diff !== expected_diff || Borrow !== expected_borrow) begin
                $display("TEST FAILED: A=%b, B=%b | Expected: Diff=%b, Borrow=%b | Got: Diff=%b, Borrow=%b", 
                         A, B, expected_diff, expected_borrow, Diff, Borrow);
            end else begin
                $display("TEST PASSED: A=%b, B=%b | Diff=%b, Borrow=%b", 
                         A, B, Diff, Borrow);
            end
        end
    endtask

    initial begin
        $display("Starting 8-bit Subtractor Testbench...");

        // Test Case 1: 0 - 0
        A = 8'b00000000; B = 8'b00000000;
        #10 check_result(8'b00000000, 1'b0);

        // Test Case 2: 1 - 0
        A = 8'b00000001; B = 8'b00000000;
        #10 check_result(8'b00000001, 1'b0);

        // Test Case 3: 0 - 1
        A = 8'b00000000; B = 8'b00000001;
        #10 check_result(8'b11111111, 1'b1);

        // Test Case 4: 10 - 5
        A = 8'b00001010; B = 8'b00000101;
        #10 check_result(8'b00000101, 1'b0);

        // Test Case 5: 1 - 255
        A = 8'b00000001; B = 8'b11111111;
        #10 check_result(8'b00000010, 1'b1); // Fixed

        // Test Case 6: 255 - 255
        A = 8'b11111111; B = 8'b11111111;
        #10 check_result(8'b00000000, 1'b0);

        // Test Case 7: 10 - 10
        A = 8'b00001010; B = 8'b00001010;
        #10 check_result(8'b00000000, 1'b0); // Fixed

        // Test Case 8: 128 - 255
        A = 8'b10000000; B = 8'b11111111;
        #10 check_result(8'b10000001, 1'b1); // Fixed

        // Test Case 9: 85 - 170
        A = 8'b01010101; B = 8'b10101010;
        #10 check_result(8'b10101011, 1'b1); // Fixed

        // Test Case 10: 240 - 15
        A = 8'b11110000; B = 8'b00001111;
        #10 check_result(8'b11100001, 1'b0);

        // Test Case 11: 15 - 1
        A = 8'b00001111; B = 8'b00000001;
        #10 check_result(8'b00001110, 1'b0);

        // Test Case 12: 107 - 37
        A = 8'b01101011; B = 8'b00100101;
        #10 check_result(8'b01000110, 1'b0); // Fixed

        // Test Case 13: 50 - 100
        A = 8'b00110010; B = 8'b01100100;
        #10 check_result(8'b11001110, 1'b1); // Fixed

        $display("All tests completed.");
        $finish;
    end
endmodule