`timescale 1ns / 1ps

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
        /*
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
        */
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

        /*
        */

        // End simulation
        $finish;
    end
    
endmodule