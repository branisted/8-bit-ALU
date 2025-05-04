`timescale 1ns/1ps

module alu_add (
    input clk,                      // Clock signal
    input reset,                    // Reset signal
    input start,                    // Start signal
    input signed [7:0] a, b,        // Operands
    output reg signed [15:0] sum,   // Output sum (extend to 16 bits)
    output reg done                 // Done flag
);
    // FSM state definitions
    localparam IDLE = 3'b000,
               INIT = 3'b001,
               CALC = 3'b010,
               DONE = 3'b011;

    reg [2:0] state, next_state;

    // Internal operands
    reg [7:0] A, B;
    reg [7:0] G, P, C;
    reg [8:0] S;  // Sum including carry-out
    reg carry_out;

    // State transitions
    always @(posedge clk) begin
        if (reset) begin
            state <= IDLE;
            done <= 0;
            sum <= 0;
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
            G <= 0;
            P <= 0;
            C <= 0;
            S <= 0;
            carry_out <= 0;
            sum <= 0;
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
                    // Generate and propagate
                    G = A & B;
                    P = A ^ B;

                    // Carry lookahead
                    C[0] = 0;
                    C[1] = G[0] | (P[0] & C[0]);
                    C[2] = G[1] | (P[1] & C[1]);
                    C[3] = G[2] | (P[2] & C[2]);
                    C[4] = G[3] | (P[3] & C[3]);
                    C[5] = G[4] | (P[4] & C[4]);
                    C[6] = G[5] | (P[5] & C[5]);
                    C[7] = G[6] | (P[6] & C[6]);
                    carry_out = G[7] | (P[7] & C[7]);

                    // Final sum
                    S = {carry_out, (P ^ C[7:0])};

                    sum <= {{8{S[8]}}, S};  // Sign-extend to 16 bits
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