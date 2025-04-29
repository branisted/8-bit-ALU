`timescale 1ns/1ps

module alu_div (
    input clk,              // Clock signal
    input reset,            // Reset signal
    input start,            // Start signal
    input signed [7:0] a,   // Dividend (8-bit signed)
    input signed [7:0] b,   // Divisor (8-bit signed)
    output reg signed [15:0] quotient, // Quotient (16-bit signed)
    output reg done         // Done flag
);
    // Internal registers
    reg [15:0] R;           // Remainder (16 bits, unsigned during computation)
    reg [15:0] D;           // Divisor (16 bits, aligned, unsigned)
    reg [7:0] Q;            // Quotient bits (8 bits)
    reg [2:0] count;        // Step counter (0 to 7)
    reg [2:0] state, next_state;
    reg sign;               // Sign of quotient (a[7] XOR b[7])
    reg [7:0] abs_a;        // Absolute value of dividend
    reg [7:0] abs_b;        // Absolute value of divisor

    // State definitions
    localparam IDLE = 3'b000,
               INIT = 3'b001,
               CALC = 3'b010,
               DONE = 3'b011;

    // State transition
    always @(posedge clk) begin
        if (reset) begin
            state <= IDLE;
            done <= 0;
            quotient <= 0;
        end else begin
            state <= next_state;
        end
    end

    // Next state logic
    always @(*) begin
        case (state)
            IDLE: next_state = start ? INIT : IDLE;
            INIT: next_state = (abs_b == 0) ? DONE : CALC;
            CALC: next_state = (count == 3'd7) ? DONE : CALC;
            DONE: next_state = IDLE;
            default: next_state = IDLE;
        endcase
    end

    // Datapath and control logic
    always @(posedge clk) begin
        if (reset) begin
            R <= 0;
            D <= 0;
            Q <= 0;
            count <= 0;
            done <= 0;
            quotient <= 0;
            sign <= 0;
            abs_a <= 0;
            abs_b <= 0;
        end else begin
            case (state)
                IDLE: begin
                    done <= 0;  // Clear done flag
                end

                INIT: begin
                    // Compute sign and absolute values
                    sign <= a[7] ^ b[7];  // Quotient sign
                    abs_a <= a[7] ? -a : a;  // |a|
                    abs_b <= b[7] ? -b : b;  // |b|
                    if (abs_b == 0) begin
                        // Division by zero: set max/min based on dividend sign
                        quotient <= a[7] ? 16'h8000 : 16'h7FFF;  // -32768 or 32767
                        done <= 1;
                    end else begin
                        // Initialize for division
                        R <= {8'b0, abs_a};  // Zero-extend |a|
                        D <= {abs_b, 7'b0};  // Shift |b| left by 7 bits
                        Q <= 0;              // Clear quotient bits
                        count <= 0;
                        done <= 0;
                    end
                end

                CALC: begin
                    // Step 1: Subtract divisor
                    R <= R - D;
                    // Step 2: Check remainder and set quotient bit
                    if (R[15] == 0) begin  // R >= 0
                        Q <= {Q[6:0], 1'b1};  // Append 1 to quotient
                    end else begin
                        R <= R + D;           // Restore remainder
                        Q <= {Q[6:0], 1'b0};  // Append 0 to quotient
                    end
                    // Step 3: Shift divisor right
                    D <= D >> 1;
                    // Step 4: Update counter and finalize
                    count <= count + 1;
                    if (count == 3'd7) begin
                        // Apply sign to quotient
                        quotient <= sign ? -{{8{Q[7]}}, Q} : {{8{Q[7]}}, Q};
                        done <= 1;
                    end
                end

                DONE: begin
                    done <= 0;  // Clear done flag
                end

                default: begin
                    done <= 0;
                    quotient <= quotient;  // Hold quotient
                end
            endcase
        end
    end
endmodule