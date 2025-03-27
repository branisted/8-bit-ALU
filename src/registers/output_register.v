`timescale 1ns / 1ps

module output_register (
    input clk,                // Clock signal
    input reset,              // Reset signal (active high)
    input [15:0] in_data,     // 16-bit input data (ALU result)
    input load,               // Load signal (active high)
    output reg [15:0] out_data // 16-bit output data (register content)
);
    always @(posedge clk or posedge reset) begin
        if (reset) 
            out_data <= 16'b0;   // Reset the register to 0
        else if (load) 
            out_data <= in_data; // Load the ALU result into the register
    end
endmodule
