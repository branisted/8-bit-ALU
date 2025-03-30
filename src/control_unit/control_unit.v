`timescale 1ns / 1ps

module control_unit (
    input wire clk,
    input wire rst,
    input wire start,
    input wire [1:0] opcode,  // 00: ADD/SUB, 01: MUL, 10: DIV
    input wire zero_count,    // Indicates end of iterative operations (MUL/DIV)
    output reg load,
    output reg compute,
    output reg dec_count,
    output reg reset_count,
    output reg done,
    output reg [1:0] select_op  // 00: ADD, 01: SUB, 10: MUL, 11: DIV
);

    // Define state encoding
    localparam IDLE      = 3'b000;
    localparam ADD_SUB   = 3'b001;
    localparam MUL_LOAD  = 3'b010;
    localparam MUL_EXEC  = 3'b011;
    localparam DIV_LOAD  = 3'b100;
    localparam DIV_EXEC  = 3'b101;
    localparam DONE      = 3'b110;

    // State registers
    reg [2:0] state, next_state;

    // State transition
    always @(posedge clk or posedge rst) begin
        if (rst) 
            state <= IDLE;
        else     
            state <= next_state;
    end

    // Next state logic
    always @(*) begin
        case (state)
            IDLE: 
                if (start) begin
                    case (opcode)
                        2'b00: next_state = ADD_SUB;    // Addition/Subtraction
                        2'b01: next_state = MUL_LOAD;   // Booth Multiplication
                        2'b10: next_state = DIV_LOAD;   // Non-Restoring Division
                        default: next_state = IDLE;
                    endcase
                end else next_state = IDLE;
            
            ADD_SUB: next_state = DONE;  // One-cycle execution
            
            MUL_LOAD: next_state = MUL_EXEC;
            MUL_EXEC: next_state = zero_count ? DONE : MUL_EXEC;

            DIV_LOAD: next_state = DIV_EXEC;
            DIV_EXEC: next_state = zero_count ? DONE : DIV_EXEC;

            DONE: next_state = IDLE;

            default: next_state = IDLE;
        endcase
    end

    // Output logic
    always @(*) begin
        // Default signals
        load = 0; compute = 0; dec_count = 0; reset_count = 0;
        done = 0; select_op = 2'b00;

        case (state)
            IDLE: begin end
            
            ADD_SUB: begin
                load = 1; 
                select_op = opcode; // 00 for ADD, 01 for SUB
            end

            MUL_LOAD: begin
                load = 1; 
                reset_count = 1;
                select_op = 2'b10; // Multiplication
            end
            
            MUL_EXEC: begin
                compute = 1;
                dec_count = 1;
            end
            
            DIV_LOAD: begin
                load = 1; 
                reset_count = 1;
                select_op = 2'b11; // Division
            end
            
            DIV_EXEC: begin
                compute = 1;
                dec_count = 1;
            end

            DONE: begin
                done = 1;
            end
        endcase
    end
endmodule