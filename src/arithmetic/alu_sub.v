`timescale 1ns/1ps

// ALU SUB
module alu_sub (
    input clk,
    input signed [7:0] a, b,
    input start,
    output reg signed [15:0] diff,
    output reg done
);
    reg [7:0] a_reg, b_reg;
    reg started = 0;

    wire [7:0] B_complement;
    wire [7:0] cla_diff;
    wire Cout;

    twos_complement bcomp (
        .a(b_reg),
        .not_a(B_complement)
    );

    cla_8bit cla_sub (
        .a(a_reg),
        .b(B_complement),
        .cin(1'b1),
        .sum(cla_diff),
        .cout(Cout)
    );

    always @(posedge clk) begin
        if (start && !started) begin
            a_reg <= a;
            b_reg <= b;
            started <= 1;
            done <= 0;
        end else if (started) begin
            diff <= {{8{cla_diff[7]}}, cla_diff};
            done <= 1;
            started <= 0;
        end else begin
            done <= 0;
        end
    end
endmodule