`timescale 1ns/1ps

module alu_control(
    input clk,
    input reset,
    input start,
    input [2:0] opcode,          // 3-bit operation code
    input mul_done,              // signal from multiplier
    input div_done,              // signal from divider
    output reg load_a,
    output reg load_b,
    output reg load_out,
    output reg done,
    output reg start_add,
    output reg start_sub,
    output reg start_mul,
    output reg start_div,
    output reg start_and,
    output reg start_or,
    output reg start_xor,
    output reg [2:0] sel_op      // 3-bit control for MUX/operation
);

    // FSM state encoding
    localparam IDLE    = 3'b000,
               LOAD    = 3'b001,
               EXECUTE = 3'b010,
               WAIT    = 3'b011,
               WRITE   = 3'b100,
               DONE    = 3'b101;

    reg [2:0] state, next_state;

    // === State Register ===
    always @(posedge clk or posedge reset) begin
        if (reset)
            state <= IDLE;
        else
            state <= next_state;
    end

    // === Next State Logic ===
    always @(*) begin
        case (state)
            IDLE:    next_state = start ? LOAD : IDLE;
            LOAD:    next_state = EXECUTE;
            EXECUTE: begin
                if (opcode == 3'b010 || opcode == 3'b011) // MUL or DIV
                    next_state = WAIT;
                else
                    next_state = WRITE;
            end
            WAIT: begin
                if ((opcode == 3'b010 && mul_done) || (opcode == 3'b011 && div_done))
                    next_state = WRITE;
                else
                    next_state = WAIT;
            end
            WRITE:   next_state = DONE;
            DONE:    next_state = IDLE;
            default: next_state = IDLE;
        endcase
    end

    // === Output Logic ===
    always @(*) begin
        // Default values
        load_a = 0;
        load_b = 0;
        load_out = 0;
        done = 0;
        start_add = 0;
        start_sub = 0;
        start_mul = 0;
        start_div = 0;
        start_and = 0;
        start_or  = 0;
        start_xor = 0;
        sel_op = opcode;

        case (state)
            LOAD: begin
                load_a = 1;
                load_b = 1;
            end
            EXECUTE: begin
                case (opcode)
                    3'b000: start_add = 1;
                    3'b001: start_sub = 1;
                    3'b010: start_mul = 1;
                    3'b011: start_div = 1;
                    3'b100: start_and = 1;
                    3'b101: start_or  = 1;
                    3'b110: start_xor = 1;
                endcase
            end
            WRITE: begin
                load_out = 1;
            end
            DONE: begin
                done = 1;
            end
        endcase
    end

endmodule