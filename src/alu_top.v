module alu_top (
    input signed [7:0] A, B,
    input [1:0] op,
    output signed [15:0] result
);
    arithmetic_unit au (.A(A), .B(B), .op(op), .result(result));
endmodule