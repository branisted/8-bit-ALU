module alu_8bit (
    input clk,                // Clock signal
    input reset,              // Reset signal (active high)
    input [7:0] A, B,         // 8-bit operands
    input [1:0] op_sel,       // Operation selector (00=ADD, 01=SUB, 10=MUL, 11=DIV)
    input load,               // Load result signal
    output reg [15:0] result, // 16-bit result (for MUL & DIV)
    output reg done           // Completion signal for MUL & DIV
);

    // Internal Wires
    wire [15:0] sum, diff, product, quotient;
    wire add_done, sub_done, mul_done, div_done;
    wire load_alu;           // Control signal to load ALU result
    wire [1:0] alu_op;       // ALU operation selector
    
    // Instantiate the control unit
    control_unit CTRL_UNIT (
        .clk(clk),
        .reset(reset),
        .op_sel(op_sel),
        .load_alu(load_alu),
        .alu_op(alu_op),
        .done(done)
    );

    // Add operation (8-bit Adder)
    adder_8bit ADDER (
        .A(A),
        .B(B),
        .sum(sum)
    );

    // Subtract operation (8-bit Subtractor)
    subtractor_8bit SUBTRACTOR (
        .A(A),
        .B(B),
        .diff(diff)
    );

    // Booth Radix-4 Multiplier
    multiplier_booth_radix4 MULTIPLIER (
        .clk(clk),
        .reset(reset),
        .multiplicand(A),
        .multiplier(B),
        .product(product),
        .done(mul_done)
    );

    // Non-restoring Division
    divider_non_restoring DIVIDER (
        .clk(clk),
        .reset(reset),
        .dividend(A),
        .divisor(B),
        .quotient(quotient),
        .done(div_done)
    );

    // 4-to-1 multiplexer to select the operation result
    mux4to1_16bit MUX (
        .in0(sum),
        .in1(diff),
        .in2(product),
        .in3(quotient),
        .sel(alu_op),  // Select based on ALU operation
        .out(result)
    );

    // Done signal logic
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            result <= 16'b0;
            done <= 0;
        end
        else if (load_alu) begin
            case (alu_op)
                2'b00: result <= sum;       // ADD
                2'b01: result <= diff;      // SUB
                2'b10: result <= product;   // MUL
                2'b11: result <= quotient;  // DIV
            endcase
        end
    end

endmodule