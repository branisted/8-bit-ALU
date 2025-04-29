`timescale 1ns/1ps

// ALU ADD
module alu_add (
    input clk,
    input signed [7:0] a, b,
    input start,
    output reg signed [15:0] sum,
    output reg done
);
    reg [7:0] a_reg, b_reg;
    reg started = 0;

    wire [7:0] cla_sum;
    wire Cout;

    cla_8bit cla_inst (
        .a(a_reg),
        .b(b_reg),
        .cin(1'b0),
        .sum(cla_sum),
        .cout(Cout)
    );

    always @(posedge clk) begin
        if (start && !started) begin
            a_reg <= a;
            b_reg <= b;
            started <= 1;
            done <= 0;
        end else if (started) begin
            sum <= {{8{cla_sum[7]}}, cla_sum};
            done <= 1;
            started <= 0;
        end else begin
            done <= 0;
        end
    end
endmodule