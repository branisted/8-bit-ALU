module tb_divider;
    reg [7:0] A, B;       // Inputs for the divider
    wire [7:0] quotient, remainder;  // Outputs from the divider

    // Instantiate the non-restoring divider module
    divider uut (
        .A(A),
        .B(B),
        .quotient(quotient),
        .remainder(remainder)
    );

    initial begin
        // Test case 1: 8 / 2 = 4, remainder = 0
        A = 8'b00001000; B = 8'b00000010; #10;
        $display("A = %d, B = %d -> Quotient = %d, Remainder = %d", A, B, quotient, remainder);
        
        // Test case 2: 7 / 3 = 2, remainder = 1
        A = 8'b00000111; B = 8'b00000011; #10;
        $display("A = %d, B = %d -> Quotient = %d, Remainder = %d", A, B, quotient, remainder);

        // Test case 3: 10 / 3 = 3, remainder = 1
        A = 8'b00001010; B = 8'b00000011; #10;
        $display("A = %d, B = %d -> Quotient = %d, Remainder = %d", A, B, quotient, remainder);

        // Test case 4: 8 / 0 (division by zero)
        A = 8'b00001000; B = 8'b00000000; #10;
        $display("A = %d, B = %d -> Quotient = %d, Remainder = %d", A, B, quotient, remainder);
        
        // End of simulation
        $finish;
    end
endmodule
