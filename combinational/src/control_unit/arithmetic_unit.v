module arithmetic_unit (
    input signed [7:0] A, B,                // Operand A and B
    input [1:0] op,                         // Operation select
    input add_en, sub_en, mul_en, div_en,    // Control signals from control_unit
    output reg signed [15:0] result         // Result of the operation
);
    wire signed [7:0] sum, diff, quotient, remainder;
    wire signed [15:0] product;

    // Instantiate the functional units (Adder, Subtractor, Multiplier, Divider)
    adder adder_inst (.A(A), .B(B), .Cin(1'b0), .Sum(sum), .Cout());
    subtractor subtractor_inst (.A(A), .B(B), .Diff(diff), .Borrow());
    multiplier multiplier_inst (.A(A), .B(B), .result(product));
    divider divider_inst (.dividend(A), .divisor(B), .quotient(quotient), .remainder(remainder));

    always @(*) begin
        // Default: No operation
        result = 16'b0;

        // Perform the operation based on the control signals
        if (add_en) begin
            result = {8'b0, sum};    // Addition result
        end else if (sub_en) begin
            result = {{8{diff[7]}}, diff};   // Subtraction result
        end else if (mul_en) begin
            result = product;        // Multiplication result
        end else if (div_en) begin
            result = {quotient, remainder}; // Division result
        end
    end
endmodule
