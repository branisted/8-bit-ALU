`timescale 1ns / 1ps

module divider (
    input [7:0] A,        // 8-bit numerator (A)
    input [7:0] B,        // 8-bit denominator (B)
    output reg [7:0] quotient,  // 8-bit quotient (A / B)
    output reg [7:0] remainder  // 8-bit remainder (A % B)
);

    always @ (A, B) begin
        if (B != 0) begin
            quotient = A / B;       // Perform division (quotient)
            remainder = A % B;      // Perform modulo operation (remainder)
        end else begin
            quotient = 8'b0;       // Handle division by zero
            remainder = 8'b0;      // Handle division by zero
        end
    end

endmodule
