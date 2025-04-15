module arith_right_shifter (
    output wire [15:0] out,
    input wire [15:0] in
);

    // out[15] is directly connected to in[15] (sign preservation)
    or (out[15], in[15], 1'b0);  // Using OR with 0 to structurally "copy" in[15]

    // Shift bits: out[i] = in[i+1] for i = 0 to 14
    or (out[14], in[15], 1'b0);  // out[14] = in[15]
    or (out[13], in[14], 1'b0);  // out[13] = in[14]
    or (out[12], in[13], 1'b0);  // out[12] = in[13]
    or (out[11], in[12], 1'b0);  // out[11] = in[12]
    or (out[10], in[11], 1'b0);  // out[10] = in[11]
    or (out[9],  in[10], 1'b0);  // out[9]  = in[10]
    or (out[8],  in[9],  1'b0);  // out[8]  = in[9]
    or (out[7],  in[8],  1'b0);  // out[7]  = in[8]
    or (out[6],  in[7],  1'b0);  // out[6]  = in[7]
    or (out[5],  in[6],  1'b0);  // out[5]  = in[6]
    or (out[4],  in[5],  1'b0);  // out[4]  = in[5]
    or (out[3],  in[4],  1'b0);  // out[3]  = in[4]
    or (out[2],  in[3],  1'b0);  // out[2]  = in[3]
    or (out[1],  in[2],  1'b0);  // out[1]  = in[2]
    or (out[0],  in[1],  1'b0);  // out[0]  = in[1]

endmodule
