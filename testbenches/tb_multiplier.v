`timescale 1ns / 1ps

module tb_multiplier;
    // Declare the inputs and outputs
    reg [7:0] A, B;     // 8-bit inputs for multiplicand and multiplier
    wire [15:0] result; // 16-bit result

    // Instantiate the Booth multiplier module
    multiplier uut (
        .A(A),
        .B(B),
        .result(result)
    );

    initial begin
        // Test Case 1: Multiplication of 0 and 0
        A = 8'b00000000;
        B = 8'b00000000;
        #10;
        $display("A=00000000, B=00000000 -> Result=%b", result);

        // Test Case 2: Multiplication of 1 and 1
        A = 8'b00000001;
        B = 8'b00000001;
        #10;
        $display("A=00000001, B=00000001 -> Result=%b", result);

        // Test Case 3: Multiplication of 2 and 3
        A = 8'b00000010;
        B = 8'b00000011;
        #10;
        $display("A=00000010, B=00000011 -> Result=%b", result);

        // Test Case 4: Multiplication of 15 and 15
        A = 8'b00001111;
        B = 8'b00001111;
        #10;
        $display("A=00001111, B=00001111 -> Result=%b", result);

        // Test Case 5: Multiplication of 255 and 255
        A = 8'b11111111;
        B = 8'b11111111;
        #10;
        $display("A=11111111, B=11111111 -> Result=%b", result);

        // Add more test cases as needed
        
        // End simulation after 50 ns
        $finish;
    end
endmodule