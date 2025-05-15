`timescale 1ns/1ps

module alu_div (
    input clk,
    input reset,
    input start,
    input signed [7:0] a,
    input signed [7:0] b,
    output reg signed [15:0] quotient,
    output reg done
);

    localparam IDLE = 3'b000,
               INIT = 3'b001,
               CALC = 3'b010,
               DONE = 3'b011;

    reg [2:0] state, next_state;
    reg [3:0] count;
    reg a_sign, b_sign;
    reg [15:0] A;
    reg [7:0] Q;
    reg [7:0] M;

    // Semnale intermediare
    reg [15:0] next_A;
    reg [7:0] next_Q;

    always @(posedge clk) begin
        if (reset) begin
            state <= IDLE;
            done <= 1'b0;
            quotient <= 16'sd0;
        end else begin
            state <= next_state;
        end
    end

    always @(*) begin
        case (state)
            IDLE: next_state = start ? INIT : IDLE;
            INIT: next_state = (b == 0) ? DONE : CALC;
            CALC: next_state = (count == 4'd8) ? DONE : CALC;
            DONE: next_state = IDLE;
            default: next_state = IDLE;
        endcase
    end

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
                    done <= 1'b0;
                end

                INIT: begin
                    a_sign <= a[7];
                    b_sign <= b[7];
                    Q <= a[7] ? -a : a;
                    M <= b[7] ? -b : b;
                    A <= 16'd0;
                    count <= 4'd0;
                    done <= 1'b0;
                end

                CALC: begin
                    // 1. Se shifteaza la stanga {A[14:0], Q, 1'b0}
                    {next_A, next_Q} = {A[14:0], Q, 1'b0};

                    // 2. Operatii bazate pe primul bit
                    if (next_A[15] == 1'b0) begin
                        // Se scade M
                        next_A = next_A - {8'd0, M};
                        next_Q[0] = 1'b1;
                    end else begin
                        // Se aduna M
                        next_A = next_A + {8'd0, M};
                        next_Q[0] = 1'b0;
                    end

                    // 3. Setarea produslui
                    A <= next_A;
                    Q <= next_Q;
                    count <= count + 4'd1;
                end

                DONE: begin
                    // Cazul in care impartitorul e 0 (full behavioural)
                    if (b == 0) begin
                        quotient <= 16'sd0;
                    end else begin
                        // Se corecteaza semnul
                        if (a_sign ^ b_sign)
                            quotient <= -{8'd0, Q};
                        else
                            quotient <= {8'd0, Q};
                    end
                    done <= 1'b1;
                end

                default: begin
                    done <= 1'b0;
                end
            endcase
        end
    end

endmodule