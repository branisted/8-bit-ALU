`timescale 1ns / 1ps

module tb_subtractor;
    // Testbench signals
    reg [7:0] A, B;
    wire [7:0] Diff;
    wire Borrow;
    
    // Instantiate the DUT (Device Under Test)
    subtractor uut (
        .A(A),
        .B(B),
        .Diff(Diff),
        .Borrow(Borrow)
    );
    
    // Test stimulus
    initial begin
        
        // Apply test cases
        // Apply test cases
        A = 8'b00000000; B = 8'b00000000; #10; $display("A=%d, B=%d -> Diff=%d, Borrow=%d", $signed(A), $signed(B), $signed(Diff), Borrow);  // 0 - 0 = 0, Cout = 0
        A = 8'b00000001; B = 8'b00000001; #10; $display("A=%d, B=%d -> Diff=%d, Borrow=%d", $signed(A), $signed(B), $signed(Diff), Borrow);  // 1 - 1 = 0, Cout = 0
        A = 8'b00001111; B = 8'b00000001; #10; $display("A=%d, B=%d -> Diff=%d, Borrow=%d", $signed(A), $signed(B), $signed(Diff), Borrow);  // 15 - 1 = 14, Cout = 0
        A = 8'b11110000; B = 8'b00001111; #10; $display("A=%d, B=%d -> Diff=%d, Borrow=%d", $signed(A), $signed(B), $signed(Diff), Borrow);  // -16 - 15 = -31, Cout = 0
        A = 8'b11111111; B = 8'b00000001; #10; $display("A=%d, B=%d -> Diff=%d, Borrow=%d", $signed(A), $signed(B), $signed(Diff), Borrow);  // -1 - 1 = -2, Cout = 0
        A = 8'b11111111; B = 8'b11111111; #10; $display("A=%d, B=%d -> Diff=%d, Borrow=%d", $signed(A), $signed(B), $signed(Diff), Borrow);  // -1 - (-1) = 0, Cout = 0
        A = 8'b00000000; B = 8'b00000001; #10; $display("A=%d, B=%d -> Diff=%d, Borrow=%d", $signed(A), $signed(B), $signed(Diff), Borrow);  // 0 - 1 = -1 (11111111), Cout = 1
        A = 8'b01111111; B = 8'b10000000; #10; $display("A=%d, B=%d -> Diff=%d, Borrow=%d", $signed(A), $signed(B), $signed(Diff), Borrow);  // 127 - (-128) = 255, Cout = 0
        A = 8'b10000000; B = 8'b01111111; #10; $display("A=%d, B=%d -> Diff=%d, Borrow=%d", $signed(A), $signed(B), $signed(Diff), Borrow);  // -128 - 127 = -255, Cout = 1
        A = 8'b10000000; B = 8'b10000000; #10; $display("A=%d, B=%d -> Diff=%d, Borrow=%d", $signed(A), $signed(B), $signed(Diff), Borrow);  // -128 - (-128) = 0, Cout = 0
        A = 8'b00000001; B = 8'b11111111; #10; $display("A=%d, B=%d -> Diff=%d, Borrow=%d", $signed(A), $signed(B), $signed(Diff), Borrow);  // 1 - (-1) = 2, Cout = 0
        A = 8'b11111111; B = 8'b00000000; #10; $display("A=%d, B=%d -> Diff=%d, Borrow=%d", $signed(A), $signed(B), $signed(Diff), Borrow);  // -1 - 0 = -1, Cout = 0
        A = 8'b01000000; B = 8'b11000000; #10; $display("A=%d, B=%d -> Diff=%d, Borrow=%d", $signed(A), $signed(B), $signed(Diff), Borrow);  // 64 - (-64) = 128, Cout = 0
        A = 8'b11000000; B = 8'b01000000; #10; $display("A=%d, B=%d -> Diff=%d, Borrow=%d", $signed(A), $signed(B), $signed(Diff), Borrow);  // -64 - 64 = -128, Cout = 1
        
        // End simulation
        $finish;
    end
    
endmodule