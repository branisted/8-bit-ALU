// Booth Radix 2 Multiplier

`timescale 1ns / 1ps

// 8-bit Register with Load Enable
module register_8bit (
    input clk,
    input rst,
    input load,
    input [7:0] d,
    output [7:0] q
);
    wire [7:0] din;
    assign din = load ? d : q;
    
    genvar i;
    generate
        for (i=0; i<8; i=i+1) begin: reg_loop
            dff dff_inst (
                .clk(clk),
                .rst(rst),
                .d(din[i]),
                .q(q[i])
            );
        end
    endgenerate
endmodule

// 1-bit D Flip-Flop
module dff (
    input clk,
    input rst,
    input d,
    output reg q
);
    always @(posedge clk or posedge rst) begin
        if (rst) q <= 1'b0;
        else q <= d;
    end
endmodule

// 3-bit Counter with Done Signal
module counter_3bit (
    input clk,
    input rst,
    input en,
    output [2:0] count,
    output done
);
    wire [2:0] next_count = count + 1;
    
    dff d0 (.clk(clk), .rst(rst), .d(en ? next_count[0] : count[0]), .q(count[0]));
    dff d1 (.clk(clk), .rst(rst), .d(en ? next_count[1] : count[1]), .q(count[1]));
    dff d2 (.clk(clk), .rst(rst), .d(en ? next_count[2] : count[2]), .q(count[2]));
    
    assign done = (count == 3'b111);
endmodule

// Control Logic
module control (
    input Q0,
    input Q_minus_1,
    output add,
    output sub
);
    wire not_Q0, not_Q_minus_1;
    not n1 (not_Q0, Q0);
    not n2 (not_Q_minus_1, Q_minus_1);
    and a1 (add, not_Q0, Q_minus_1);
    and a2 (sub, Q0, not_Q_minus_1);
endmodule

// 8-bit Adder
module adder_8bit (
    input [7:0] a,
    input [7:0] b,
    output [7:0] sum
);
    assign sum = a + b;
endmodule

// 8-bit Subtractor
module subtractor_8bit (
    input [7:0] a,
    input [7:0] b,
    output [7:0] diff
);
    assign diff = a - b;
endmodule

// 3-to-1 Multiplexer
module mux_3to1 (
    input sel_add,
    input sel_sub,
    input [7:0] in_adder,
    input [7:0] in_subtractor,
    input [7:0] in_default,
    output [7:0] out
);
    wire [7:0] w1, w2;
    assign w1 = sel_add ? in_adder : in_default;
    assign w2 = sel_sub ? in_subtractor : w1;
    assign out = w2;
endmodule

// 16-bit Arithmetic Right Shifter
module shifter_16bit (
    input [15:0] in,
    output [15:0] out
);
    assign out = {in[15], in[15:1]};
endmodule

// Booth Radix-2 Multiplier Top Module
module multiplier (
    input clk,
    input rst,
    input start,        // New start signal
    input [7:0] multiplier,
    input [7:0] multiplicand,
    output [15:0] product,
    output done         // Expose done signal
);
    wire [7:0] A_out, Q_out, M_out;
    wire Q_minus_1_out;
    wire [2:0] count;
    wire add, sub;
    wire [7:0] adder_out, subtractor_out, mux_out;
    wire [15:0] shifted;
    
    // New control signals
    wire load_initial = start;
    wire load_shift = ~done && !load_initial;

    // Registers
    register_8bit A (.clk(clk), .rst(rst), .load(load_shift), 
                  .d(shifted[15:8]), .q(A_out));
    register_8bit Q (.clk(clk), .rst(rst), .load(load_initial | load_shift),
                    .d(load_initial ? multiplier : shifted[7:0]), .q(Q_out));
    register_8bit M (.clk(clk), .rst(rst), .load(1'b1), 
                    .d(multiplicand), .q(M_out));
    dff Q_minus_1 (.clk(clk), .rst(rst), .d(Q_out[0]), .q(Q_minus_1_out));
    
    // Counter
    counter_3bit cnt (.clk(clk), .rst(rst | load_initial), .en(load_shift),
                    .count(count), .done(done));
    
    // Control Logic
    control ctrl (.Q0(Q_out[0]), .Q_minus_1(Q_minus_1_out), .add(add), .sub(sub));
    
    // Adder and Subtractor
    adder_8bit add_unit (.a(A_out), .b(M_out), .sum(adder_out));
    subtractor_8bit sub_unit (.a(A_out), .b(M_out), .diff(subtractor_out));
    
    // Mux
    mux_3to1 mux (.sel_add(add), .sel_sub(sub), .in_adder(adder_out), 
                 .in_subtractor(subtractor_out), .in_default(A_out), .out(mux_out));
    
    // Shifter
    shifter_16bit shft (.in({mux_out, Q_out}), .out(shifted));
    
    // Output
    assign product = {A_out, Q_out};
endmodule

/*

module multiplier (
    input clk, 
    input rst, 
    input start,
    input [7:0] multiplicand, 
    input [7:0] multiplier,
    output [15:0] product,
    output done
);

    reg [8:0] A;         // 9-bit accumulator
    reg [8:0] Q;         // 9-bit multiplier (8 bits + 1 appended 0)
    reg Q_prev;          // Previous multiplier bit
    reg [3:0] count;     // 0-9 iterations
    
    reg add, sub;       // Control signals
    wire [8:0] adder_result;

    // Booth encoder
    always @(*) begin
        case ({Q_prev, Q[0]})
            2'b01: {add, sub} = 2'b10;  // Add
            2'b10: {add, sub} = 2'b01;  // Subtract
            default: {add, sub} = 2'b00; 
        endcase
    end

    // Sign-extend multiplicand and handle subtraction
    wire [8:0] m_ext = {multiplicand[7], multiplicand};
    wire [8:0] b_in = sub ? ~m_ext : m_ext;
    wire cin = sub;
    assign adder_result = A + b_in + cin;

    // Shift register and control logic
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            A <= 0;
            Q <= 0;
            Q_prev <= 0;
            count <= 0;
        end else if (start) begin
            A <= 0;
            Q <= {multiplier, 1'b0};  // Append 0 for 9 iterations
            Q_prev <= 0;
            count <= 0;
        end else if (count < 9) begin
            if (add || sub) begin
                // Apply add/sub and shift
                A <= {adder_result[8], adder_result[8:1]};
                Q <= {adder_result[0], Q[8:1]};
            end else begin
                // Shift right without operation
                A <= {A[8], A[8:1]};
                Q <= {A[0], Q[8:1]};
            end
            Q_prev <= Q[0];
            count <= count + 1;
        end
    end

    assign done = (count == 9);
    assign product = ~{A[7:0], Q[8:1]} + 1;  // Negate the product
    //assign product = {A[8], A[7:1], Q[8:1]};  // 16-bit product
endmodule

*/