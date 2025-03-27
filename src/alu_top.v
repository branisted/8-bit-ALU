`timescale 1ns / 1ps

module alu_top (
    input [7:0] A,          // 8-bit input A
    input [7:0] B,          // 8-bit input B
    input [1:0] op_sel,     // Operation selector (00=ADD, 01=SUB, 10=MUL, 11=DIV)
    input clk,              // Clock signal
    input reset,            // Reset signal (active high)
    output [15:0] result    // 16-bit result from the ALU
);

    // Internal signals for operation outputs
    wire [7:0] sum, diff, quotient, remainder;
    wire [15:0] product;
    wire carry_out, borrow_out;
    wire load_alu, done;
    wire [1:0] alu_op;

    // Intermediate signals for the input registers
    wire [7:0] A_reg, B_reg;
    reg [15:0] alu_out; // Change this to reg, since we are assigning it in an always block

    // Instantiate input registers for A and B
    input_register A_reg_inst (
        .clk(clk),
        .reset(reset),
        .in_data(A),
        .load(1'b1), // Load input data (always load on each clock cycle)
        .out_data(A_reg)
    );

    input_register B_reg_inst (
        .clk(clk),
        .reset(reset),
        .in_data(B),
        .load(1'b1), // Load input data (always load on each clock cycle)
        .out_data(B_reg)
    );

    // Instantiate control unit to decide ALU operation
    control_unit control_inst (
        .op_sel(op_sel),
        .clk(clk),
        .reset(reset),
        .load_alu(load_alu),
        .alu_op(alu_op),
        .done(done)
    );

    // Instantiate the adder, subtractor, multiplier, and divider
    adder adder_inst (
        .A(A_reg),
        .B(B_reg),
        .Cin(1'b0),  // No carry-in for addition (use 1-bit zero)
        .Sum(sum),
        .Cout(carry_out)
    );

    subtractor subtractor_inst (
        .A(A_reg),
        .B(B_reg),
        .Diff(diff),
        .Borrow(borrow_out)
    );

    multiplier multiplier_inst (
        .A(A_reg),
        .B(B_reg),
        .Product(product)
    );

    divider divider_inst (
        .A(A_reg),
        .B(B_reg),
        .quotient(quotient),
        .remainder(remainder)
    );

    // Select output based on alu_op (ADD, SUB, MUL, DIV)
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            alu_out <= 16'b0;
        end else begin
            case (alu_op)
                2'b00: alu_out <= {8'b0, sum};          // ADD
                2'b01: alu_out <= {8'b0, diff};         // SUB
                2'b10: alu_out <= product;              // MUL
                2'b11: alu_out <= {quotient, remainder}; // DIV
                default: alu_out <= 16'b0;
            endcase
        end
    end

    // Instantiate output register to store the result
    output_register output_reg_inst (
        .clk(clk),
        .reset(reset),
        .in_data(alu_out),
        .load(load_alu),  // Load result into the output register when done
        .out_data(result)
    );

endmodule
