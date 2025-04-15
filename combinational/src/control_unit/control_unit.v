module control_unit (
    input [1:0] op,                // Operation select input
    output reg add_en,             // Enable signal for adder
    output reg sub_en,             // Enable signal for subtractor
    output reg mul_en,             // Enable signal for multiplier
    output reg div_en              // Enable signal for divider
);
    always @(*) begin
        // Default: all functional units are disabled
        add_en = 0;
        sub_en = 0;
        mul_en = 0;
        div_en = 0;

        case (op)
            2'b00: add_en = 1;   // Enable adder for addition
            2'b01: sub_en = 1;   // Enable subtractor for subtraction
            2'b10: mul_en = 1;   // Enable multiplier for multiplication
            2'b11: div_en = 1;   // Enable divider for division
        endcase
    end
endmodule