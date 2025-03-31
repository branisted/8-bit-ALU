`timescale 1ns / 1ps

module tb_twos_complement;
    reg [7:0] in;
    wire [7:0] out;
    
    // Instantiate the twos_complement module
    twos_complement UUT (.out(out), .in(in));

    initial begin
        // Display Header
        $display("Time | Input  | 2's Complement Output");
        $monitor("%4t | %b (%d) | %b (%d)", $time, in, $signed(in), out, $signed(out));

        // Test Cases
        in = 8'b00000000; #10; //  0 →   0
        in = 8'b00000001; #10; //  1 →  -1
        in = 8'b00000010; #10; //  2 →  -2
        in = 8'b00001000; #10; //  8 →  -8
        in = 8'b01111111; #10; // 127 → -127
        in = 8'b10000000; #10; // -128 (special case)
        in = 8'b10000001; #10; // -127 → 127
        in = 8'b11111111; #10; // -1 →  1
        
        #10;
        $finish;
    end
endmodule
