`timescale 1ns / 1ps

module gp_logic (
    input A, B,
    output G, P
);
    and (G, A, B);
    xor (P, A, B);
endmodule