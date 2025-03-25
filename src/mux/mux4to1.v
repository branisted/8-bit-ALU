module mux4to1_16bit (
    input [15:0] in0, in1, in2, in3,  // 16-bit inputs
    input [1:0] sel,                  // 2-bit selector
    output reg [15:0] out             // 16-bit output
);
    always @(*) begin
        case(sel)
            2'b00: out = in0;  // Select input 0
            2'b01: out = in1;  // Select input 1
            2'b10: out = in2;  // Select input 2
            2'b11: out = in3;  // Select input 3
            default: out = 16'b0;  // Default case (optional)
        endcase
    end
endmodule