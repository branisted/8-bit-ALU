`timescale 1ns/1ps

module alu_mul (
    input clk,              // Clock signal
    input reset,            // Reset signal
    input start,            // Start signal
    input signed [7:0] a,   // Multiplicand (8-bit signed)
    input signed [7:0] b,   // Multiplier (8-bit signed)
    output reg signed [15:0] product, // Product (16-bit signed)
    output reg done         // Done flag
);
    // Module-level declarations
    reg signed [7:0] M;     // Multiplicand
    reg signed [7:0] A;     // Accumulator (upper part of product)
    reg [7:0] Q;            // Multiplier (lower part of product)
    reg Q_m1;               // Extra bit for Booth's algorithm
    reg [2:0] count;        // Counter (0 to 7 for 8 steps)
    reg [2:0] state, next_state;
    // Moved declarations from CALC block
    reg signed [7:0] temp_A;
    reg signed [7:0] shifted_A;
    reg [7:0] shifted_Q;
    reg shifted_Q_m1;

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
            product <= 0;
        end else begin
            state <= next_state;
        end
    end

    // Next state logic
    always @(*) begin
        case (state)
            IDLE: next_state = start ? INIT : IDLE;
            INIT: next_state = CALC;
            CALC: next_state = (count == 3'd7) ? DONE : CALC;
            DONE: next_state = IDLE;
            default: next_state = IDLE;
        endcase
    end

    // Datapath and control logic
    always @(posedge clk) begin
        if (reset) begin
            M <= 0;
            A <= 0;
            Q <= 0;
            Q_m1 <= 0;
            count <= 0;
            done <= 0;
            product <= 0;
            temp_A <= 0;
            shifted_A <= 0;
            shifted_Q <= 0;
            shifted_Q_m1 <= 0;
        end else begin
            case (state)
                IDLE: begin
                    done <= 0;  // Clear done flag
                end

                INIT: begin
                    M <= a;        // Load multiplicand
                    A <= 0;        // Initialize accumulator
                    Q <= b;        // Load multiplier
                    Q_m1 <= 0;     // Initialize extra bit
                    count <= 0;    // Reset counter
                    done <= 0;
                end

                CALC: begin
                    // Step 1: Operation based on current and previous bits
                    case ({Q[0], Q_m1})
                        2'b01: temp_A = A + M;   // Add multiplicand
                        2'b10: temp_A = A - M;   // Subtract multiplicand
                        default: temp_A = A;     // No operation
                    endcase

                    // Step 2: Arithmetic right shift of {A, Q, Q_m1}
                    shifted_A = {temp_A[7], temp_A[7:1]};  // Preserve sign
                    shifted_Q = {temp_A[0], Q[7:1]};
                    shifted_Q_m1 = Q[0];

                    // Update registers
                    A <= shifted_A;
                    Q <= shifted_Q;
                    Q_m1 <= shifted_Q_m1;
                    count <= count + 1;

                    // Step 3: Set product after final step
                    if (count == 3'd7) begin
                        product <= {shifted_A, shifted_Q};
                        done <= 1;
                    end
                end

                DONE: begin
                    done <= 0;  // Clear done flag
                end

                default: begin
                    done <= 0;
                    product <= product;  // Hold product value
                end
            endcase
        end
    end
endmodule