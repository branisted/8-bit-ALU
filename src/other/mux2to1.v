`timescale 1ns / 1ps

module mux2to1(input a, input b, input sel, output y);
    assign y = (~sel & a) | (sel & b);
endmodule