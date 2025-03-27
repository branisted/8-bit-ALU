`timescale 1ns / 1ps

module control_unit (
    input [1:0] op_sel,      // Operation selector (00=ADD, 01=SUB, 10=MUL, 11=DIV)
    input clk,               // Clock signal
    input reset,             // Reset signal (active high)
    output reg load_alu,     // Control signal to load ALU result
    output reg [1:0] alu_op, // ALU operation selector (0=ADD, 1=SUB, 2=MUL, 3=DIV)
    output reg done          // Completion signal for MUL & DIV
);

    // Control logic for different operations
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            load_alu <= 0;
            alu_op <= 2'b00;  // Default operation: ADD
            done <= 0;
        end else begin
            case (op_sel)
                2'b00: begin  // ADD operation
                    alu_op <= 2'b00; // ALU operation: ADD
                    load_alu <= 1;   // Load the result into the ALU
                    done <= 1;       // Operation done
                end
                2'b01: begin  // SUB operation
                    alu_op <= 2'b01; // ALU operation: SUB
                    load_alu <= 1;   // Load the result into the ALU
                    done <= 1;       // Operation done
                end
                2'b10: begin  // MUL operation
                    alu_op <= 2'b10; // ALU operation: MUL
                    load_alu <= 1;   // Load the result into the ALU
                    done <= 0;       // Wait for multiplication to complete
                end
                2'b11: begin  // DIV operation
                    alu_op <= 2'b11; // ALU operation: DIV
                    load_alu <= 1;   // Load the result into the ALU
                    done <= 0;       // Wait for division to complete
                end
                default: begin
                    alu_op <= 2'b00; // Default: ADD
                    load_alu <= 0;   // No operation
                    done <= 0;
                end
            endcase
        end
    end
endmodule
