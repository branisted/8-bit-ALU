`timescale 1ns / 1ps

module tb_subtractor;
    // Testbench signals
    reg [7:0] A, B;
    wire [7:0] Diff;
    wire Cout;
    
    // Instantiate the DUT (Device Under Test)
    subtractor uut (
        .A(A),
        .B(B),
        .Diff(Diff),
        .Cout(Cout)
    );
    
    // Test stimulus
    initial begin
        
        // Apply test cases
        A = 8'b00000000; B = 8'b00000000; #10; $display("A=%d, B=%d -> Diff=%d, Cout=%d", A, B, Diff, Cout);
        A = 8'b00000001; B = 8'b00000001; #10; $display("A=%d, B=%d -> Diff=%d, Cout=%d", A, B, Diff, Cout);
        A = 8'b00001111; B = 8'b00000001; #10; $display("A=%d, B=%d -> Diff=%d, Cout=%d", A, B, Diff, Cout);
        A = 8'b11110000; B = 8'b00001111; #10; $display("A=%d, B=%d -> Diff=%d, Cout=%d", A, B, Diff, Cout);
        A = 8'b11111111; B = 8'b00000001; #10; $display("A=%d, B=%d -> Diff=%d, Cout=%d", A, B, Diff, Cout);
        A = 8'b11111111; B = 8'b11111111; #10; $display("A=%d, B=%d -> Diff=%d, Cout=%d", A, B, Diff, Cout);
        
        // End simulation
        $finish;
    end
    
endmodule