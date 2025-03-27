`timescale 1ns / 1ps

module tb_register;

    // Inputs
    reg clk;
    reg reset;
    reg [7:0] in_data;
    reg load;

    // Outputs
    wire [7:0] out_data;

    // Instantiate the Unit Under Test (UUT)
    input_register uut (
        .clk(clk),
        .reset(reset),
        .in_data(in_data),
        .load(load),
        .out_data(out_data)
    );

    // Clock generation (50 MHz clock)
    always begin
        #5 clk = ~clk; // Toggle clock every 5 ns for a 10 ns period (50 MHz)
    end

    // Stimulus
    initial begin
        // Initialize inputs
        clk = 0;
        reset = 0;
        in_data = 8'b00000000;
        load = 0;

        // Apply reset
        reset = 1; #10;
        reset = 0; #10;

        // Apply some test cases
        in_data = 8'b10101010; load = 1; #10; // Load 10101010 into register
        load = 0; #10;
        in_data = 8'b11110000; load = 1; #10; // Load 11110000 into register
        load = 0; #10;

        // Check behavior with load disabled
        in_data = 8'b00001111; load = 0; #10; // No load, output should remain 11110000
        #10;

        // Apply reset again
        reset = 1; #10;
        reset = 0; #10;

        // Finish simulation
        $finish;
    end

    // Monitor the outputs
    initial begin
        $monitor("Time = %0t | reset = %b | in_data = %b | load = %b | out_data = %b", $time, reset, in_data, load, out_data);
    end

endmodule
