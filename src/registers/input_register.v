module input_register (
    input clk,                // Clock signal
    input reset,              // Reset signal (active high)
    input [7:0] in_data,      // 8-bit input data
    input load,               // Load signal (active high)
    output reg [7:0] out_data // 8-bit output data (register content)
);
    always @(posedge clk or posedge reset) begin
        if (reset) 
            out_data <= 8'b0;    // Reset the register to 0
        else if (load) 
            out_data <= in_data; // Load the input data into the register
    end
endmodule