`timescale 1ns/1ps

module alu_mul (
    input clk,
    input reset,
    input start,
    input signed [7:0] a,  // Multiplicand
    input signed [7:0] b,  // Multiplier
    output reg signed [15:0] product,  // Product result
    output reg done  // Done flag
);
    reg signed [7:0] multiplicand;
    reg signed [8:0] multiplier;  // 9 bits for Booth's algorithm
    reg signed [16:0] accumulator;  // 17 bits for intermediate results
    reg [3:0] count;  // Counter for iterations
    reg [3:0] state, next_state;

    // State encoding
    localparam IDLE  = 4'b0000,
               INIT  = 4'b0001,
               CALC  = 4'b0010,
               DONE  = 4'b0100;

    // State Register
    always @(posedge clk) begin
        if (reset) begin
            state <= IDLE;
            done <= 0;
            product <= 0;  // Ensure product is initialized
        end else begin
            state <= next_state;
        end
    end

    // Next State Logic
    always @(*) begin
        case (state)
            IDLE: next_state = start ? INIT : IDLE;
            INIT: next_state = CALC;
            CALC: next_state = (count == 4'd8) ? DONE : CALC;
            DONE: next_state = start ? INIT : IDLE;
            default: next_state = IDLE;
        endcase
    end

    // Datapath and Control Logic
    always @(posedge clk) begin
        if (reset) begin
            multiplicand <= 0;
            multiplier <= 0;
            accumulator <= 0;
            product <= 0;
            count <= 0;
            done <= 0;
        end else begin
            case (state)
                IDLE: begin
                    done <= 0;  // Clear done in IDLE
                    product <= product;  // Hold product
                end

                INIT: begin
                    multiplicand <= a;
                    multiplier <= {b, 1'b0};  // Append 0 for Booth's
                    accumulator <= 0;
                    count <= 0;
                    done <= 0;
                end

                CALC: begin
                    case (multiplier[1:0])
                        2'b01: accumulator <= accumulator + ({{9{multiplicand[7]}}, multiplicand} << count);
                        2'b10: accumulator <= accumulator - ({{9{multiplicand[7]}}, multiplicand} << count);
                        default: accumulator <= accumulator;  // 00 or 11: no operation
                    endcase
                    multiplier <= multiplier >>> 1;  // Explicit arithmetic right shift
                    count <= count + 1;
                end

                DONE: begin
                    product <= accumulator[15:0];  // Final product
                    done <= 1;
                end

                default: begin
                    done <= 0;
                    product <= product;  // Hold product
                end
            endcase
        end
    end
endmodule