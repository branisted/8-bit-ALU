`timescale 1ns/1ps

module alu_div (
    input clk,                // Clock signal
    input reset,              // Reset signal
    input start,              // Start signal
    input signed [7:0] a,     // Dividend
    input signed [7:0] b,     // Divisor
    output reg signed [15:0] quotient, // Quotient
    output reg done            // Done flag
);

    // State definitions
    localparam IDLE = 3'b000,
               INIT = 3'b001,
               CALC = 3'b010,
               DONE = 3'b011;

    reg [2:0] state, next_state;   // FSM state
    reg [3:0] count;               // Counter (0 to 7 for 8 steps)
    reg a_sign, b_sign;            // Original signs
    reg [15:0] A;                  // Remainder register
    reg [7:0] Q;                   // Quotient register (abs value)
    reg [7:0] M;                   // Divisor register (abs value)

    // Intermediate signals for next-state logic
    reg [15:0] next_A;
    reg [7:0] next_Q;

    // State transition logic
    always @(posedge clk) begin
        if (reset) begin
            state <= IDLE;
            done <= 1'b0;
            quotient <= 16'sd0;
        end else begin
            state <= next_state;
        end
    end

    // Next state logic
    always @(*) begin
        case (state)
            IDLE: next_state = start ? INIT : IDLE;
            INIT: next_state = (b == 0) ? DONE : CALC;
            CALC: next_state = (count == 4'd8) ? DONE : CALC;
            DONE: next_state = IDLE;
            default: next_state = IDLE;
        endcase
    end

    // Datapath and control logic
    always @(posedge clk) begin
        if (reset) begin
            count <= 4'd0;
            A <= 16'd0;
            Q <= 8'd0;
            M <= 8'd0;
            a_sign <= 1'b0;
            b_sign <= 1'b0;
            done <= 1'b0;
            quotient <= 16'sd0;
        end else begin
            case (state)
                IDLE: begin
                    done <= 1'b0;  // Clear done flag
                end

                INIT: begin
                    a_sign <= a[7];
                    b_sign <= b[7];
                    Q <= a[7] ? -a : a;  // Load absolute value of a
                    M <= b[7] ? -b : b;  // Load absolute value of b
                    A <= 16'd0;  // Initialize remainder
                    count <= 4'd0;  // Reset counter
                    done <= 1'b0;
                end

                CALC: begin
                    // Shift left {A, Q}
                    {next_A, next_Q} = {A[14:0], Q, 1'b0};

                    // Adjust A and Q based on remainder sign
                    if (next_A[15] == 1'b0) begin
                        next_A = next_A - {8'd0, M};  // Subtract M
                        next_Q[0] = 1'b1;             // Set Q[0] to 1
                    end else begin
                        next_A = next_A + {8'd0, M};  // Add M
                        next_Q[0] = 1'b0;             // Set Q[0] to 0
                    end

                    // Commit values
                    A <= next_A;
                    Q <= next_Q;
                    count <= count + 4'd1;
                end

                DONE: begin
                    // Division by zero handling
                    if (b == 0) begin
                        quotient <= 16'sd0;
                    end else begin
                        // Apply final sign to quotient
                        if (a_sign ^ b_sign)
                            quotient <= -{8'd0, Q};
                        else
                            quotient <= {8'd0, Q};
                    end
                    done <= 1'b1;  // Set done flag
                end

                default: begin
                    done <= 1'b0;
                end
            endcase
        end
    end

endmodule