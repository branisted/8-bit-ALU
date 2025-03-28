`timescale 1ns / 1ps

module tb_multiplier();
    reg clk, rst, start;
    reg [7:0] multiplier, multiplicand;
    wire [15:0] product;
    wire done;
    
    multiplier uut (
        .clk(clk),
        .rst(rst),
        .start(start),
        .multiplier(multiplier),
        .multiplicand(multiplicand),
        .product(product),
        .done(done)
    );
    
    // Clock generation
    always #5 clk = ~clk;
    
    initial begin
        clk = 0;
        rst = 1;
        start = 0;
        #20 rst = 0;
        
        test_case(8'd0, 8'd0);
        test_case(8'd255, 8'd255);
        test_case(8'd170, 8'd85);
        test_case(8'd123, 8'd45);
        test_case(8'd128, 8'd128);
        
        #100 $finish;
    end
    
    task test_case(input [7:0] a, b);
        begin
            multiplier = a;
            multiplicand = b;
            start = 1;
            @(posedge clk);
            start = 0;
            
            wait(done);
            $display("Test Case: %d * %d", a, b);
            $display("Expected: %d, Actual: %d", 
                    $unsigned(a) * $unsigned(b), product);
            $display("---------------------------");
        end
    endtask
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