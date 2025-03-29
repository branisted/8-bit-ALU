`timescale 1ns / 1ps

// Testbench (same as before, just updated module name)
module tb_multiplier;
    reg clk;
    reg rst;
    reg start;
    reg [7:0] multiplicand;
    reg [7:0] multiplier;
    wire [15:0] product;
    wire done;
    
    // Instantiate the Booth multiplier
    multiplier uut (
        .clk(clk),
        .rst(rst),
        .start(start),
        .multiplicand(multiplicand),
        .multiplier(multiplier),
        .product(product),
        .done(done)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 100MHz clock
    end
    
    // Test procedure
    initial begin
        // Initialize signals
        rst = 1;
        start = 0;
        multiplicand = 8'b0;
        multiplier = 8'b0;
        
        #20 rst = 0;
        
        // Test case 1: Basic positive multiplication (5 * 3 = 15)
        #10;
        multiplicand = 8'd5;
        multiplier = 8'd3;
        start = 1;
        #10 start = 0;
        @(posedge done);
        #10 $display("Test 1: %d * %d = %d (Expected: 15)", 
                    $signed(multiplicand), $signed(multiplier), $signed(product));
        
        // Test case 2: Negative * Positive (-4 * 6 = -24)
        #20;
        multiplicand = -8'd4;
        multiplier = 8'd6;
        start = 1;
        #10 start = 0;
        @(posedge done);
        #10 $display("Test 2: %d * %d = %d (Expected: -24)", 
                    $signed(multiplicand), $signed(multiplier), $signed(product));
        
        // Test case 3: Negative * Negative (-3 * -7 = 21)
        #20;
        multiplicand = -8'd3;
        multiplier = -8'd7;
        start = 1;
        #10 start = 0;
        @(posedge done);
        #10 $display("Test 3: %d * %d = %d (Expected: 21)", 
                    $signed(multiplicand), $signed(multiplier), $signed(product));
        
        // Test case 4: Multiply by zero (5 * 0 = 0)
        #20;
        multiplicand = 8'd5;
        multiplier = 8'd0;
        start = 1;
        #10 start = 0;
        @(posedge done);
        #10 $display("Test 4: %d * %d = %d (Expected: 0)", 
                    $signed(multiplicand), $signed(multiplier), $signed(product));
        
        // Test case 5: Maximum positive (127 * 1 = 127)
        #20;
        multiplicand = 8'd127;
        multiplier = 8'd1;
        start = 1;
        #10 start = 0;
        @(posedge done);
        #10 $display("Test 5: %d * %d = %d (Expected: 127)", 
                    $signed(multiplicand), $signed(multiplier), $signed(product));
        
        // Test case 6: Minimum negative (-128 * 1 = -128)
        #20;
        multiplicand = -8'd128;
        multiplier = 8'd1;
        start = 1;
        #10 start = 0;
        @(posedge done);
        #10 $display("Test 6: %d * %d = %d (Expected: -128)", 
                    $signed(multiplicand), $signed(multiplier), $signed(product));
        
        // Test case 7: Large numbers (50 * 50 = 2500)
        #20;
        multiplicand = 8'd50;
        multiplier = 8'd50;
        start = 1;
        #10 start = 0;
        @(posedge done);
        #10 $display("Test 7: %d * %d = %d (Expected: 2500)", 
                    $signed(multiplicand), $signed(multiplier), $signed(product));
        
        // Test case 8: Negative edge case (-128 * -1 = 128)
        #20;
        multiplicand = -8'd128;
        multiplier = -8'd1;
        start = 1;
        #10 start = 0;
        @(posedge done);
        #10 $display("Test 8: %d * %d = %d (Expected: 128)", 
                    $signed(multiplicand), $signed(multiplier), $signed(product));
        
        // Test case 9: Both max negative (-128 * -128 = 16384)
        #20;
        multiplicand = -8'd128;
        multiplier = -8'd128;
        start = 1;
        #10 start = 0;
        @(posedge done);
        #10 $display("Test 9: %d * %d = %d (Expected: 16384)", 
                    $signed(multiplicand), $signed(multiplier), $signed(product));
        
        // Test case 10: Large negative (-50 * 50 = -2500)
        #20;
        multiplicand = -8'd50;
        multiplier = 8'd50;
        start = 1;
        #10 start = 0;
        @(posedge done);
        #10 $display("Test 10: %d * %d = %d (Expected: -2500)", 
                    $signed(multiplicand), $signed(multiplier), $signed(product));
        
        #20 $finish;
    end
endmodule


/*
module tb_multiplier;
    // Testbench signals
    reg [7:0] A, B;
    wire [15:0] Product;
    
    // Instantiate the DUT (Device Under Test)
    multiplier uut (
        .A(A),
        .B(B),
        .Product(Product)
    );
    
    // Test stimulus
    initial begin
        
        // Apply test cases
        
        A = 8'b00000000; B = 8'b00000000; #10; $display("A=%d, B=%d -> Product=%d", $signed(A), $signed(B), $signed(Product));
        A = 8'b00000001; B = 8'b00000001; #10; $display("A=%d, B=%d -> Product=%d", $signed(A), $signed(B), $signed(Product)); // 1 * 1 = 1
        A = 8'b00000010; B = 8'b00000001; #10; $display("A=%d, B=%d -> Product=%d", $signed(A), $signed(B), $signed(Product)); // 2 * 1 = 2
        A = 8'b00000111; B = 8'b00000011; #10; $display("A=%d, B=%d -> Product=%d", $signed(A), $signed(B), $signed(Product)); // 7 * 3 = 21
        A = 8'b00001000; B = 8'b00001000; #10; $display("A=%d, B=%d -> Product=%d", $signed(A), $signed(B), $signed(Product)); // 8 * 8 = 64
        A = 8'b11111111; B = 8'b11111111; #10; $display("A=%d, B=%d -> Product=%d", $signed(A), $signed(B), $signed(Product)); // -1 * -1 = 1
        A = 8'b11111110; B = 8'b00000001; #10; $display("A=%d, B=%d -> Product=%d", $signed(A), $signed(B), $signed(Product)); // -2 * 1 = -2
        A = 8'b11111111; B = 8'b00000001; #10; $display("A=%d, B=%d -> Product=%d", $signed(A), $signed(B), $signed(Product)); // -1 * 1 = -1
        A = 8'b10000000; B = 8'b10000000; #10; $display("A=%d, B=%d -> Product=%d", $signed(A), $signed(B), $signed(Product)); // -128 * -128 = 16384
        A = 8'b00000001; B = 8'b11111111; #10; $display("A=%d, B=%d -> Product=%d", $signed(A), $signed(B), $signed(Product)); // 1 * -1 = -1
        A = 8'b11110000; B = 8'b00001111; #10; $display("A=%d, B=%d -> Product=%d", $signed(A), $signed(B), $signed(Product)); // -16 * 15 = -240
        A = 8'b11111100; B = 8'b11111101; #10; $display("A=%d, B=%d -> Product=%d", $signed(A), $signed(B), $signed(Product)); // -4 * -3 = 12
        A = 8'b01010101; B = 8'b10101010; #10; $display("A=%d, B=%d -> Product=%d", $signed(A), $signed(B), $signed(Product)); // 85 * -86 = -7310
        A = 8'b01010101; B = 8'b00000000; #10; $display("A=%d, B=%d -> Product=%d", $signed(A), $signed(B), $signed(Product)); // 85 * 0 = 0
        A = 8'b11111111; B = 8'b11110000; #10; $display("A=%d, B=%d -> Product=%d", $signed(A), $signed(B), $signed(Product)); // -1 * -16 = 16
        A = 8'b10101010; B = 8'b01010101; #10; $display("A=%d, B=%d -> Product=%d", $signed(A), $signed(B), $signed(Product)); // -86 * 85 = -7310
        
        A = 8'b00000000; B = 8'b00000000; #10; $display("A=%d, B=%d -> Product=%d", A, B, Product);
        A = 8'b00000001; B = 8'b00000001; #10; $display("A=%d, B=%d -> Product=%d", A, B, Product); // 1 * 1 = 1
        A = 8'b00000010; B = 8'b00000001; #10; $display("A=%d, B=%d -> Product=%d", A, B, Product); // 2 * 1 = 2
        A = 8'b00000111; B = 8'b00000011; #10; $display("A=%d, B=%d -> Product=%d", A, B, Product); // 7 * 3 = 21
        A = 8'b00001000; B = 8'b00001000; #10; $display("A=%d, B=%d -> Product=%d", A, B, Product); // 8 * 8 = 64
        A = 8'b11111111; B = 8'b11111111; #10; $display("A=%d, B=%d -> Product=%d", A, B, Product); // -1 * -1 = 1
        A = 8'b11111110; B = 8'b00000001; #10; $display("A=%d, B=%d -> Product=%d", A, B, Product); // -2 * 1 = -2
        A = 8'b11111111; B = 8'b00000001; #10; $display("A=%d, B=%d -> Product=%d", A, B, Product); // -1 * 1 = -1
        A = 8'b10000000; B = 8'b10000000; #10; $display("A=%d, B=%d -> Product=%d", A, B, Product); // -128 * -128 = 16384
        A = 8'b00000001; B = 8'b11111111; #10; $display("A=%d, B=%d -> Product=%d", A, B, Product); // 1 * -1 = -1
        A = 8'b11110000; B = 8'b00001111; #10; $display("A=%d, B=%d -> Product=%d", A, B, Product); // -16 * 15 = -240
        A = 8'b11111100; B = 8'b11111101; #10; $display("A=%d, B=%d -> Product=%d", A, B, Product); // -4 * -3 = 12
        A = 8'b01010101; B = 8'b10101010; #10; $display("A=%d, B=%d -> Product=%d", A, B, Product); // 85 * -86 = -7310
        A = 8'b01010101; B = 8'b00000000; #10; $display("A=%d, B=%d -> Product=%d", A, B, Product); // 85 * 0 = 0
        A = 8'b11111111; B = 8'b11110000; #10; $display("A=%d, B=%d -> Product=%d", A, B, Product); // -1 * -16 = 16
        A = 8'b10101010; B = 8'b01010101; #10; $display("A=%d, B=%d -> Product=%d", A, B, Product); // -86 * 85 = -7310

        A = 8'b00000000; B = 8'b00000000; #10; $display("A=%b, B=%b -> Product=%b", A, B, Product);
        A = 8'b00000001; B = 8'b00000001; #10; $display("A=%b, B=%b -> Product=%b", A, B, Product); // 1 * 1 = 1
        A = 8'b00000010; B = 8'b00000001; #10; $display("A=%b, B=%b -> Product=%b", A, B, Product); // 2 * 1 = 2
        A = 8'b00000111; B = 8'b00000011; #10; $display("A=%b, B=%b -> Product=%b", A, B, Product); // 7 * 3 = 21
        A = 8'b00001000; B = 8'b00001000; #10; $display("A=%b, B=%b -> Product=%b", A, B, Product); // 8 * 8 = 64
        A = 8'b11111111; B = 8'b11111111; #10; $display("A=%b, B=%b -> Product=%b", A, B, Product); // -1 * -1 = 1
        A = 8'b11111110; B = 8'b00000001; #10; $display("A=%b, B=%b -> Product=%b", A, B, Product); // -2 * 1 = -2
        A = 8'b11111111; B = 8'b00000001; #10; $display("A=%b, B=%b -> Product=%b", A, B, Product); // -1 * 1 = -1
        A = 8'b10000000; B = 8'b10000000; #10; $display("A=%b, B=%b -> Product=%b", A, B, Product); // -128 * -128 = 16384
        A = 8'b00000001; B = 8'b11111111; #10; $display("A=%b, B=%b -> Product=%b", A, B, Product); // 1 * -1 = -1
        A = 8'b11110000; B = 8'b00001111; #10; $display("A=%b, B=%b -> Product=%b", A, B, Product); // -16 * 15 = -240
        A = 8'b11111100; B = 8'b11111101; #10; $display("A=%b, B=%b -> Product=%b", A, B, Product); // -4 * -3 = 12
        A = 8'b01010101; B = 8'b10101010; #10; $display("A=%b, B=%b -> Product=%b", A, B, Product); // 85 * -86 = -7310
        A = 8'b01010101; B = 8'b00000000; #10; $display("A=%b, B=%b -> Product=%b", A, B, Product); // 85 * 0 = 0
        A = 8'b11111111; B = 8'b11110000; #10; $display("A=%b, B=%b -> Product=%b", A, B, Product); // -1 * -16 = 16
        A = 8'b10101010; B = 8'b01010101; #10; $display("A=%b, B=%b -> Product=%b", A, B, Product); // -86 * 85 = -7310

        // End simulation
        $finish;
    end
    
endmodule
*/