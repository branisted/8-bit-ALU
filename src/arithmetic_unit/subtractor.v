module subtractor (
    input [7:0] A, B,
    output [7:0] Diff,
    output Borrow
);
    wire [7:0] B_complement;
    wire Cin = 1'b1;
    wire Cout;

    genvar i;
    generate
        for (i = 0; i < 8; i = i + 1) begin : gen_B_complement
            not (B_complement[i], B[i]);
        end
    endgenerate

    adder cla_adder (
        .A(A),
        .B(B_complement),
        .Cin(Cin),
        .Sum(Diff),
        .Cout(Cout)
    );

    not (Borrow, Cout);

endmodule