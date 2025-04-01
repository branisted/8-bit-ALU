module alu_top (
    input signed [7:0] A, B,       // Operands
    input [1:0] op,                // Operation select
    output signed [15:0] result    // ALU result
);
    // Control signals
    wire add_en, sub_en, mul_en, div_en;

    // Instantiate the control unit
    control_unit cu_inst (
        .op(op),
        .add_en(add_en),
        .sub_en(sub_en),
        .mul_en(mul_en),
        .div_en(div_en)
    );

    // Instantiate the arithmetic unit
    arithmetic_unit au_inst (
        .A(A),
        .B(B),
        .op(op),
        .add_en(add_en),
        .sub_en(sub_en),
        .mul_en(mul_en),
        .div_en(div_en),
        .result(result)
    );
endmodule
