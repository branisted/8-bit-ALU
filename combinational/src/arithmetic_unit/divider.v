module divider(
    input signed [7:0] dividend,
    input signed [7:0] divisor,
    output reg signed [7:0] quotient,
    output reg signed [7:0] remainder
);
    integer i;
    reg signed [15:0] temp_dividend;
    reg signed [7:0] temp_divisor;
    reg signed [7:0] quotient_unsigned;
    reg dividend_sign, divisor_sign;

    always @(*) begin
        // Handle division by zero
        if (divisor == 0) begin
            quotient = 8'b0;
            remainder = 8'b0;
        end 
        // Handle division by -1 explicitly
        else if (divisor == -1) begin
            quotient = (dividend == -128) ? 8'd127 : -dividend; // Avoid overflow
            remainder = 8'b0;
        end 
        else begin
            // Track signs for correct quotient calculation
            dividend_sign = dividend[7];
            divisor_sign = divisor[7];

            // Work with absolute values
            temp_dividend = {8'b0, (dividend_sign ? -dividend : dividend)};
            temp_divisor = (divisor_sign ? -divisor : divisor);

            // Initialize quotient
            quotient_unsigned = 8'b0;

            for (i = 0; i < 8; i = i + 1) begin
                // Left shift remainder and bring down next bit
                temp_dividend = temp_dividend << 1;
                temp_dividend[0] = dividend[7-i];

                // Perform non-restoring subtraction
                if (temp_dividend[15:8] >= temp_divisor) begin
                    temp_dividend[15:8] = temp_dividend[15:8] - temp_divisor;
                    quotient_unsigned[7-i] = 1'b1; // Set quotient bit
                end
            end

            // Restore signs for final quotient and remainder
            quotient = (dividend_sign ^ divisor_sign) ? -quotient_unsigned : quotient_unsigned;
            remainder = dividend_sign ? -temp_dividend[15:8] : temp_dividend[15:8];
        end
    end
endmodule
