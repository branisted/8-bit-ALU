`timescale 1ns / 1ps

module tb_adder;
    // Testbench signals
    reg [7:0] A, B;
    reg Cin;
    wire [7:0] Sum;
    wire Cout;
    
    // Instantiate the DUT (Device Under Test)
    adder uut (
        .A(A),
        .B(B),
        .Cin(Cin),
        .Sum(Sum),
        .Cout(Cout)
    );
    
    // Test stimulus
    initial begin
        
        // Apply test cases
        A = 8'b00000000; B = 8'b00000000; Cin = 0; #10; $display("A=%d, B=%d, Cin=%d -> Sum=%d, Cout=%d", A, B, Cin, Sum, Cout);
        A = 8'b00000001; B = 8'b00000001; Cin = 0; #10; $display("A=%d, B=%d, Cin=%d -> Sum=%d, Cout=%d", A, B, Cin, Sum, Cout);
        A = 8'b00001111; B = 8'b00000001; Cin = 0; #10; $display("A=%d, B=%d, Cin=%d -> Sum=%d, Cout=%d", A, B, Cin, Sum, Cout);
        A = 8'b11110000; B = 8'b00001111; Cin = 0; #10; $display("A=%d, B=%d, Cin=%d -> Sum=%d, Cout=%d", A, B, Cin, Sum, Cout);
        A = 8'b11111111; B = 8'b00000001; Cin = 0; #10; $display("A=%d, B=%d, Cin=%d -> Sum=%d, Cout=%d", A, B, Cin, Sum, Cout);
        A = 8'b11111111; B = 8'b11111111; Cin = 1; #10; $display("A=%d, B=%d, Cin=%d -> Sum=%d, Cout=%d", A, B, Cin, Sum, Cout);
        
        // End simulation
        $finish;
    end
    
endmodule