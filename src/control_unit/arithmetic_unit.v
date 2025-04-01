module arithmetic_unit (
    input signed [7:0] A, B,
    input [1:0] op,
    output signed [15:0] result
);
    wire signed [7:0] sum, diff, quotient, remainder;
    wire signed [15:0] product;

    adder adder_inst (.A(A), .B(B), .Cin(1'b0), .Sum(sum), .Cout());
    subtractor subtractor_inst (.A(A), .B(B), .Diff(diff), .Borrow());
    multiplier multiplier_inst (.A(A), .B(B), .result(product));
    divider divider_inst (.dividend(A), .divisor(B), .quotient(quotient), .remainder(remainder));

    assign result = (op == 2'b00) ? {8'b0, sum} :
                    (op == 2'b01) ? {8'b0, diff} :
                    (op == 2'b10) ? product :
                    (op == 2'b11) ? {quotient, remainder} :
                    16'b0;
endmodule
