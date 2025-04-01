module tb_divider;
    reg signed [7:0] dividend, divisor;
    wire signed [7:0] quotient, remainder;

    non_restoring_divider uut (
        .dividend(dividend), 
        .divisor(divisor), 
        .quotient(quotient), 
        .remainder(remainder)
    );

    initial begin
        $monitor("Time=%0t | Dividend=%d, Divisor=%d | Quotient=%d, Remainder=%d",
                 $time, dividend, divisor, quotient, remainder);
        
        // Test cases
        dividend = 100; divisor = 5;   #10;
        dividend = -100; divisor = 5;  #10;
        dividend = 100; divisor = -5;  #10;
        dividend = -100; divisor = -5; #10;
        dividend = 127; divisor = 3;   #10;
        dividend = -128; divisor = 2;  #10;
        dividend = 45; divisor = 7;    #10;
        dividend = 0; divisor = 10;    #10;
        dividend = 50; divisor = 0;    #10; // Should be handled correctly
        dividend = -128; divisor = -1; #10;

        $finish;
    end
endmodule
