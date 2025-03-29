// Booth Radix 2 Multiplier

`timescale 1ns / 1ps

// Basic components first
module mux_16bit (
    input wire [15:0] in0,
    input wire [15:0] in1,
    input wire sel,
    output wire [15:0] out
);
    assign out = sel ? in1 : in0;
endmodule

module adder_16bit (
    input wire [15:0] a,
    input wire [15:0] b,
    output wire [15:0] sum
);
    assign sum = a + b;
endmodule

module subtractor_16bit (
    input wire [15:0] a,
    input wire [15:0] b,
    output wire [15:0] diff
);
    assign diff = a - b;
endmodule

module register_16bit (
    input wire clk,
    input wire load,
    input wire [15:0] in,
    output reg [15:0] out
);
    always @(posedge clk)
        if (load) out <= in;
endmodule

module register_8bit (
    input wire clk,
    input wire load,
    input wire [7:0] in,
    output reg [7:0] out
);
    always @(posedge clk)
        if (load) out <= in;
endmodule

module register_1bit (
    input wire clk,
    input wire load,
    input wire in,
    output reg out
);
    always @(posedge clk)
        if (load) out <= in;
endmodule

module counter_4bit (
    input wire clk,
    input wire load,
    input wire dec,
    input wire [3:0] in,
    output reg [3:0] out
);
    always @(posedge clk) begin
        if (load) out <= in;
        else if (dec) out <= out - 1;
    end
endmodule

// Main Booth Multiplier
module multiplier (
    input wire clk,
    input wire rst,
    input wire start,
    input wire [7:0] multiplicand,
    input wire [7:0] multiplier,
    output wire [15:0] product,
    output wire done
);

    // Internal wires
    wire [15:0] A_out, A_in, add_out, sub_out, mux_out;
    wire [7:0] Q_out, Q_in;
    wire Q_1_out, Q_1_in;
    wire [3:0] count_out;
    wire [1:0] booth_control;
    
    // Control signals
    wire load, compute, zero_count;
    wire [15:0] extended_multiplicand = { {8{multiplicand[7]}}, multiplicand};
    
    // Controller
    assign load = start;
    assign zero_count = (count_out == 4'b0);
    assign compute = ~start & ~zero_count;
    assign done = zero_count;
    assign booth_control = {Q_out[0], Q_1_out};
    
    // Datapath
    register_16bit A_reg (
        .clk(clk),
        .load(load | compute),
        .in(A_in),
        .out(A_out)
    );
    
    register_8bit Q_reg (
        .clk(clk),
        .load(load | compute),
        .in(Q_in),
        .out(Q_out)
    );
    
    register_1bit Q_1_reg (
        .clk(clk),
        .load(load | compute),
        .in(Q_1_in),
        .out(Q_1_out)
    );
    
    counter_4bit counter (
        .clk(clk),
        .load(load),
        .dec(compute),
        .in(4'd8),
        .out(count_out)
    );
    
    // Arithmetic operations
    adder_16bit adder (
        .a(A_out),
        .b(extended_multiplicand),
        .sum(add_out)
    );
    
    subtractor_16bit subtractor (
        .a(A_out),
        .b(extended_multiplicand),
        .diff(sub_out)
    );
    
    // Booth control - simplified to single mux with proper precedence
    assign mux_out = (booth_control == 2'b01) ? add_out :
                    (booth_control == 2'b10) ? sub_out :
                    A_out;
    
    // Correct arithmetic right shift
    assign A_in = load ? 16'b0 : {mux_out[15], mux_out[15:1]};
    assign Q_in = load ? multiplier : {mux_out[0], Q_out[7:1]};
    assign Q_1_in = load ? 1'b0 : Q_out[0];
    
    assign product = {A_out[7:0], Q_out};

endmodule

/*
module multiplier (
    input [7:0] A,          // Multiplicand
    input [7:0] B,          // Multiplier
    output reg [15:0] P      // Product
);
    reg [7:0] A_neg;         // Negative of A (2's complement)
    reg [7:0] B_reg;         // Temporary register for B
    reg Q_1;                 // Previous bit of Q (initialized to 0)
    integer i;

    // A's negative form (2's complement)
    always @ (A) begin
        A_neg = ~A + 1;
    end
    
    always @ (A, B) begin
        B_reg = B;
        P = 16'b0;           // Initialize the product to 0
        Q_1 = 0;             // Initialize Q_1 to 0

        // Booth's algorithm main loop (8 iterations)
        for (i = 0; i < 8; i = i + 1) begin
            // Check the current two bits (B[0] and Q_1)
            case ({B_reg[0], Q_1})
                2'b01: P = P + (A << i);   // Add A shifted
                2'b10: P = P - (A << i);   // Subtract A shifted
                default: ;                  // No operation
            endcase

            // Shift the product and the multiplier (B_reg) right by 1
            {Q_1, B_reg} = {B_reg[7], B_reg[7:1]}; // Arithmetic right shift B
            P = P >>> 1;  // Arithmetic right shift product (P)
        end
    end
endmodule
*/

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