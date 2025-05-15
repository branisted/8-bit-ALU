`timescale 1ns/1ps

module alu_mul (
    input clk,
    input reset,
    input start,
    input signed [7:0] a,
    input signed [7:0] b,
    output reg signed [15:0] product,
    output reg done
);
    
    reg signed [7:0] M;
    reg signed [7:0] A;
    reg [7:0] Q;
    reg Q_m1;
    reg [2:0] count;
    reg [2:0] state, next_state;
    
    reg signed [7:0] temp_A;
    reg signed [7:0] shifted_A;
    reg [7:0] shifted_Q;
    reg shifted_Q_m1;

    localparam IDLE = 3'b000,
               INIT = 3'b001,
               CALC = 3'b010,
               DONE = 3'b011;

    always @(posedge clk) begin
        if (reset) begin
            state <= IDLE;
            done <= 0;
            product <= 0;
        end else begin
            state <= next_state;
        end
    end

    always @(*) begin
        case (state)
            IDLE: next_state = start ? INIT : IDLE;
            INIT: next_state = CALC;
            CALC: next_state = (count == 3'd7) ? DONE : CALC;
            DONE: next_state = IDLE;
            default: next_state = IDLE;
        endcase
    end

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
                    done <= 0;
                end

                INIT: begin
                    M <= a;
                    A <= 0;
                    Q <= b;
                    Q_m1 <= 0;
                    count <= 0;
                    done <= 0;
                end

                CALC: begin
                    // 1: Operatie bazata pe bitii curenti
                    case ({Q[0], Q_m1})
                        // Adaugam multiplicandul
                        2'b01: temp_A = A + M;
                        // Scadem multiplicandul
                        2'b10: temp_A = A - M;
                        // Nici o operatie
                        default: temp_A = A;
                    endcase

                    // 2. Shiftare aritmetica la dreapta a {A, Q, Q_m1}, cu pastrarea bitului de semn
                    shifted_A = {temp_A[7], temp_A[7:1]};
                    shifted_Q = {temp_A[0], Q[7:1]};
                    shifted_Q_m1 = Q[0];

                    // Registri updatati
                    A <= shifted_A;
                    Q <= shifted_Q;
                    Q_m1 <= shifted_Q_m1;
                    count <= count + 1;

                    // 3. Setarea produsului dupa 8 iteratii
                    if (count == 3'd7) begin
                        product <= {shifted_A, shifted_Q};
                        done <= 1;
                    end
                end

                DONE: begin
                    done <= 0;
                end

                default: begin
                    done <= 0;
                    product <= product;
                end
            endcase
        end
    end
endmodule