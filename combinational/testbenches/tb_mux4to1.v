`timescale 1ns / 1ps

module tb_mux4to1;

    // Testbench signals
    reg [15:0] data;   // 16-bit data input
    reg [1:0] sel;     // 2-bit selector
    wire [15:0] out;   // 16-bit output

    // Instantiate the mux4to1 module
    mux4to1 uut (
        .data(data),
        .sel(sel),
        .out(out)
    );

    // Apply test cases
    initial begin
        // Monitor the values of data, sel, and out
        $monitor("Time = %0t | data = %b | sel = %b | out = %b", $time, data, sel, out);

        // Test case 1: Select first bit of data
        data = 16'b1010101010101010;
        sel = 2'b00;
        #10;

        // Test case 2: Select second bit of data
        sel = 2'b01;
        #10;

        // Test case 3: Select third bit of data
        sel = 2'b10;
        #10;

        // Test case 4: Select fourth bit of data
        sel = 2'b11;
        #10;

        // Test case 5: Change data input and test all selector values
        data = 16'b1100110011001100;
        sel = 2'b00;
        #10;

        sel = 2'b01;
        #10;

        sel = 2'b10;
        #10;

        sel = 2'b11;
        #10;

        // End the simulation
        $finish;
    end

endmodule
