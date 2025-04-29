`timescale 1ns/1ps

module alu_control (
    input  wire        clk,
    input  wire        reset,
    input  wire        start,
    input  wire [2:0]  opcode,
    input  wire        op_done,

    output reg         done,
    output reg         load_a,
    output reg         load_b,
    output reg         load_out,

    output reg         start_add,
    output reg         start_sub,
    output reg         start_mul,
    output reg         start_div,
    output reg         start_and,
    output reg         start_or,
    output reg         start_xor,

    output reg [2:0]   sel_op
);

    // FSM states
    localparam IDLE    = 2'b00,
               LOAD    = 2'b01,
               EXECUTE = 2'b10,
               STORE   = 2'b11;

    reg [1:0] current_state, next_state;
    reg [2:0] opcode_latched;

    // State register, registered done, and latch opcode
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            current_state  <= IDLE;
            done           <= 1'b0;
            opcode_latched <= 3'b000;
        end else begin
            current_state  <= next_state;
            done           <= (current_state == STORE);
            if (current_state == IDLE && start)
                opcode_latched <= opcode;
        end
    end

    // Next‐state logic
    always @(*) begin
        case (current_state)
            IDLE:    next_state = start   ? LOAD    : IDLE;
            LOAD:    next_state = EXECUTE;
            EXECUTE: next_state = op_done ? STORE   : EXECUTE;
            STORE:   next_state = IDLE;
            default: next_state = IDLE;
        endcase
    end

    // Output logic – two‐phase handshake
    always @(*) begin
        // defaults
        load_a    = 1'b0;
        load_b    = 1'b0;
        load_out  = 1'b0;

        start_add = 1'b0;
        start_sub = 1'b0;
        start_mul = 1'b0;
        start_div = 1'b0;
        start_and = 1'b0;
        start_or  = 1'b0;
        start_xor = 1'b0;

        sel_op    = opcode_latched;

        case (current_state)
            IDLE: begin
                // nothing
            end

            LOAD: begin
                // Phase 1: clock in operands only
                load_a = 1'b1;
                load_b = 1'b1;
            end

            EXECUTE: begin
                // Phase 2: start the operation on freshly loaded data
                case (opcode_latched)
                    3'b000: start_add = 1'b1;
                    3'b001: start_sub = 1'b1;
                    3'b010: start_mul = 1'b1;
                    3'b011: start_div = 1'b1;
                    3'b100: start_and = 1'b1;
                    3'b101: start_or  = 1'b1;
                    3'b110: start_xor = 1'b1;
                    default:;
                endcase
            end

            STORE: begin
                // Phase 3: latch result and pulse done
                load_out = 1'b1;
            end
        endcase
    end

endmodule
