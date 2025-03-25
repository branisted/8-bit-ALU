module Shifter (
    input [15:0] dividend,    // 16-bit Dividend
    input [7:0] divisor,      // 8-bit Divisor
    input shift,              // Control signal to shift
    output reg [15:0] q,      // Quotient
    output reg [15:0] r       // Remainder (Dividend portion)
);
    always @(*) begin
        if (shift) begin
            q = {q[14:0], 1'b0};  // Shift left the quotient
            r = {r[14:0], 1'b0};  // Shift left the remainder
        end
    end
endmodule

module Subtractor (
    input [15:0] a,           // Remainder or dividend portion
    input [7:0] b,            // Divisor
    output reg [15:0] diff,   // Difference (result of a - b)
    output reg borrow         // Borrow indicator
);
    always @(*) begin
        if (a >= {8'b0, b}) begin
            diff = a - {8'b0, b};
            borrow = 0;  // No borrow if a >= b
        end else begin
            diff = a + (16'b1 << 8) - {8'b0, b};  // Add to perform subtraction with borrow
            borrow = 1;  // Borrow occurred
        end
    end
endmodule

module divider_non_restoring (
    input [15:0] dividend,  // 16-bit Dividend
    input [7:0] divisor,    // 8-bit Divisor
    output reg [7:0] quotient, // 8-bit Quotient
    output reg [7:0] remainder // 8-bit Remainder
);
    reg [15:0] q, r; // Temporary registers for quotient and remainder
    reg borrow;      // Borrow flag to decide addition or subtraction
    wire [15:0] diff; // Difference after subtraction

    // Instantiate Subtractor
    Subtractor sub (.a(r), .b(divisor), .diff(diff), .borrow(borrow));

    // Instantiate Shifter
    Shifter shift (.dividend(dividend), .divisor(divisor), .shift(1'b1), .q(q), .r(r));

    always @(dividend or divisor) begin
        q = 16'b0;
        r = dividend;
        quotient = 8'b0;
        
        // Iterate 8 times for 8-bit division
        for (integer i = 0; i < 8; i = i + 1) begin
            // Shift left the remainder and quotient
            shift.shift = 1'b1; // Shifting
            q = shift.q;
            r = shift.r;
            
            // Subtract or Add based on the current state of r
            if (borrow == 0) begin
                // No borrow, so quotient bit is 1
                quotient[i] = 1'b1;
                r = diff;  // Use the result of subtraction
            end else begin
                // Borrow occurred, so quotient bit is 0
                quotient[i] = 1'b0;
                r = diff;  // Restore
            end
        end
    end
endmodule