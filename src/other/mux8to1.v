`timescale 1ns / 1ps

module mux8to1(input [7:0] in, input [2:0] sel, output y);
    wire [3:0] l1;
    wire [1:0] l2;
    mux2to1 m0(in[0], in[1], sel[0], l1[0]);
    mux2to1 m1(in[2], in[3], sel[0], l1[1]);
    mux2to1 m2(in[4], in[5], sel[0], l1[2]);
    mux2to1 m3(in[6], in[7], sel[0], l1[3]);
    mux2to1 m4(l1[0], l1[1], sel[1], l2[0]);
    mux2to1 m5(l1[2], l1[3], sel[1], l2[1]);
    mux2to1 m6(l2[0], l2[1], sel[2], y);
endmodule