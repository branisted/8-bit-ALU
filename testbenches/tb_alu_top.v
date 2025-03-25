module tb_alu_8bit;

    // Testbench signals
    reg clk;
    reg reset;
    reg [7:0] A, B;
    reg [1:0] op_sel;
    reg load;
    wire [15:0] result;
    wire done;

    // Instantiate the ALU
    alu_8bit uut (
        .clk(clk),
        .reset(reset),
        .A(A),
        .B(B),
        .op_sel(op_sel),
        .load(load),
        .result(result),
        .done(done)
    );

    // Clock generation (50 MHz)
    always begin
        #10 clk = ~clk; // 50 MHz clock with 10 ns period
    end

    // Test procedure
    initial begin
        // Initialize signals
        clk = 0;
        reset = 0;
        A = 8'b00000000;  // Operand A
        B = 8'b00000000;  // Operand B
        op_sel = 2'b00;   // Start with ADD operation
        load = 0;

        // Apply reset
        reset = 1;
        #20 reset = 0;

        // Test ADD operation (A + B)
        A = 8'b00000001;  // A = 1
        B = 8'b00000001;  // B = 1
        op_sel = 2'b00;   // ADD
        load = 1;
        #20 load = 0;

        // Test SUB operation (A - B)
        A = 8'b00000010;  // A = 2
        B = 8'b00000001;  // B = 1
        op_sel = 2'b01;   // SUB
        load = 1;
        #20 load = 0;

        // Test MUL operation (A * B)
        A = 8'b00000010;  // A = 2
        B = 8'b00000010;  // B = 2
        op_sel = 2'b10;   // MUL
        load = 1;
        #40 load = 0;     // Wait longer for multiplication to complete

        // Test DIV operation (A / B)
        A = 8'b00000100;  // A = 4
        B = 8'b00000010;  // B = 2
        op_sel = 2'b11;   // DIV
        load = 1;
        #40 load = 0;     // Wait longer for division to complete

        // End simulation
        $finish;
    end

    // Display result at each step
    initial begin
        $monitor("At time %t: A = %b, B = %b, op_sel = %b, result = %b, done = %b", 
                 $time, A, B, op_sel, result, done);
    end

endmodule