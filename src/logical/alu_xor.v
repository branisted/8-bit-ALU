`timescale 1ns/1ps
// ALU AND
module alu_xor (
    input clk,                      // Clock signal
    input reset,                    // Reset signal
    input start,                    // Start signal
    input [7:0] a, b,        // Operands
    output reg [15:0] res,   // Output sum (extend to 16 bits)
    output reg done  
);
    // FSM state definitions
    localparam IDLE = 3'b000,
               INIT = 3'b001,
               CALC = 3'b010,
               DONE = 3'b011;

    reg [2:0] state, next_state;

    // Internal operands
    reg [7:0] A, B;

    // State transitions
    always @(posedge clk) begin
        if (reset) begin
            state <= IDLE;
            done <= 0;
            res <= 0;
        end else begin
            state <= next_state;
        end
    end

    // Next state logic
    always @(*) begin
        case (state)
            IDLE: next_state = start ? INIT : IDLE;
            INIT: next_state = CALC;
            CALC: next_state = DONE;
            DONE: next_state = IDLE;
            default: next_state = IDLE;
        endcase
    end

    // Datapath and control logic
    always @(posedge clk) begin
        if (reset) begin
            A <= 0;
            B <= 0;
            res <= 0;
            done <= 0;
        end else begin
            case (state)
                IDLE: begin
                    done <= 0;
                end

                INIT: begin
                    A <= a;
                    B <= b;
                    done <= 0;
                end

                CALC: begin
                    res <= A ^ B;
                    done <= 1;
                end

                DONE: begin
                    done <= 0;  // Clear done on next cycle
                end

                default: begin
                    done <= 0;
                end
            endcase
        end
    end
endmodule