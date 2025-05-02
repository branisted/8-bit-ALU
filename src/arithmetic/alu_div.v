`timescale 1ns/1ps

module alu_div (
    input  clk,                // Clock
    input  reset,              // Sync reset
    input  start,              // Start signal
    input  signed [7:0] a,     // Dividend
    input  signed [7:0] b,     // Divisor
    output reg signed [15:0] quotient, // Quotient
    output reg done            // Done flag
);

    //▌ State encoding
    localparam IDLE = 2'd0,
               INIT = 2'd1,
               CALC = 2'd2,
               DONE = 2'd3;

    reg [1:0]   state, next_state;
    reg  [3:0]  count;           // 0..8
    reg  a_sign, b_sign;         // original signs
    reg [15:0] A;                // remainder register
    reg  [7:0] Q;                // quotient register (abs value)
    reg  [7:0] M;                // divisor register (abs value)

    // Combinational helpers for the next-shift-and-sub/add step
    reg  [15:0] next_A;
    reg   [7:0] next_Q;

    //──────────────────────────────────
    // 1) State register
    //──────────────────────────────────
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            state    <= IDLE;
            done     <= 1'b0;
            quotient <= 16'sd0;
        end else begin
            state <= next_state;
        end
    end

    //──────────────────────────────────
    // 2) Next-state logic
    //──────────────────────────────────
    always @(*) begin
        case (state)
            IDLE:  next_state = start ? INIT : IDLE;
            INIT:  next_state = (b == 0) ? DONE : CALC;
            CALC:  next_state = (count == 4'd8) ? DONE : CALC;
            DONE:  next_state = IDLE;
            default: next_state = IDLE;
        endcase
    end

    //──────────────────────────────────
    // 3) Datapath & control
    //──────────────────────────────────
    always @(posedge clk) begin
        if (reset) begin
            // clear everything
            count    <= 4'd0;
            A        <= 16'd0;
            Q        <= 8'd0;
            M        <= 8'd0;
            a_sign   <= 1'b0;
            b_sign   <= 1'b0;
            quotient <= 16'sd0;
            done     <= 1'b0;
        end else begin
            case (state)
                //--------------------------------
                IDLE: begin
                    done <= 1'b0;
                end

                //--------------------------------
                INIT: begin
                    // latch signs and abs values
                    a_sign <= a[7];
                    b_sign <= b[7];
                    Q      <= a[7] ? -a : a;  
                    M      <= b[7] ? -b : b;
                    A      <= 16'd0;
                    count  <= 4'd0;
                    done   <= 1'b0;

                    // If b==0, we'll jump to DONE next cycle
                end

                //--------------------------------
                CALC: begin
                    // Compute next_{A,Q} in one step:
                    // 1) shift-left {A,Q}
                    // 2) if shifted_A MSB==0 subtract M, set Q[0]=1
                    //    else add M, set Q[0]=0
                    // This avoids racing between two always-blocks.
                    //
                    // first do the shift
                    { next_A, next_Q } = { A[14:0], Q, 1'b0 };

                    // then adjust remainder and quotient bit
                    if (next_A[15] == 1'b0) begin
                        next_A = next_A - { 8'd0, M };
                        next_Q[0] = 1'b1;
                    end else begin
                        next_A = next_A + { 8'd0, M };
                        next_Q[0] = 1'b0;
                    end

                    // finally, commit
                    A     <= next_A;
                    Q     <= next_Q;
                    count <= count + 4'd1;
                end

                //--------------------------------
                DONE: begin
                    // Division by zero? We forced b==0 → DONE with Q==abs(a),
                    // but here we simply return zero quotient.
                    if (b == 0) begin
                        quotient <= 16'sd0;
                    end else begin
                        // apply final sign to abs-quotient Q
                        if (a_sign ^ b_sign)
                            quotient <= -{8'd0, Q};
                        else
                            quotient <=  {8'd0, Q};
                    end
                    done <= 1'b1;
                end

            endcase
        end
    end

endmodule
