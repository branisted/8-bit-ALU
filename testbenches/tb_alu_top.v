`timescale 1ns / 1ps

module tb_alu_top();

    reg clk = 0;
    reg rst = 1;
    reg start = 0;
    reg [2:0] alu_op = 3'b000;
    reg [7:0] operand_a = 8'h00;
    reg [7:0] operand_b = 8'h00;

    wire done;
    wire [15:0] result;

    alu_top DUT (
        .clk(clk),
        .reset(rst),
        .start(start),
        .op(alu_op),
        .in_a(operand_a),
        .in_b(operand_b),
        .done(done),
        .result(result)
    );

    always #5 clk = ~clk;

    task display_state(input [127:0] opname);
        $display("T=%8t | %-14s | A=%5d, B=%5d => Result=%7d | Done=%b", 
            $time, opname, $signed(operand_a), $signed(operand_b), $signed(result), done);
    endtask

    
    initial begin
        $dumpfile("tb_alu_top.vcd");
        $dumpvars(0, tb_alu_top); 
    end

    initial begin
        $display("==== STARTING ALU TESTBENCH ====");

        #20 rst = 0;
        #20;

        // Adunare
        test_operation(3'b000, 127, 1, "ADD Overflow+");
        test_operation(3'b000, -128, -1, "ADD Overflow-");
        test_operation(3'b000, 0, 0, "ADD Zero");
        test_operation(3'b000, -50, -50, "ADD - -");

        // Scadere
        test_operation(3'b001, 127, 127, "SUB Max");
        test_operation(3'b001, 0, 0, "SUB Zero");
        test_operation(3'b001, 50, -25, "SUB + -");
        test_operation(3'b001, -50, 25, "SUB - +");
        test_operation(3'b001, -50, -50, "SUB - -");

        // Inmultire
        test_operation(3'b010, 127, 2, "MUL Overflow+");
        test_operation(3'b010, 0, 0, "MUL Zero");
        test_operation(3'b010, 10, -10, "MUL + -");
        test_operation(3'b010, -10, 10, "MUL - +");
        test_operation(3'b010, -10, -10, "MUL - -");
        test_operation(3'b010, 1, 127, "MUL 1 Max");
        test_operation(3'b010, -1, 127, "MUL -1 Max");
        test_operation(3'b010, 1, -128, "MUL 1 Min");
        test_operation(3'b010, -1, -128, "MUL -1 Min");

        // Impartire
        test_operation(3'b011, 127, 1, "DIV Max");
        test_operation(3'b011, 0, 1, "DIV ZeroNum");
        test_operation(3'b011, 100, -10, "DIV + -");
        test_operation(3'b011, -100, 10, "DIV - +");
        test_operation(3'b011, -100, -10, "DIV - -");
        test_operation(3'b011, 10, 0, "DIV Div0");
        test_operation(3'b011, 0, 0, "DIV 0/0");

        // AND, OR, XOR cu diverse combinatii de biti
        test_operation(3'b100, 8'b11110000, 8'b10101010, "AND 1");
        test_operation(3'b100, 8'b00001111, 8'b11110000, "AND 2");
        test_operation(3'b100, 8'b11111111, 8'b00000000, "AND 3");
        test_operation(3'b100, 8'b10101010, 8'b01010101, "AND 4");

        test_operation(3'b101, 8'b11110000, 8'b10101010, "OR 1");
        test_operation(3'b101, 8'b00001111, 8'b11110000, "OR 2");
        test_operation(3'b101, 8'b11111111, 8'b00000000, "OR 3");
        test_operation(3'b101, 8'b10101010, 8'b01010101, "OR 4");

        test_operation(3'b110, 8'b11110000, 8'b10101010, "XOR 1");
        test_operation(3'b110, 8'b00001111, 8'b11110000, "XOR 2");
        test_operation(3'b110, 8'b11111111, 8'b00000000, "XOR 3");
        test_operation(3'b110, 8'b10101010, 8'b01010101, "XOR 4");

        $display("==== ALU TESTBENCH COMPLETE ====");
        $stop;
    end

    task test_operation(input [2:0] op, input signed [7:0] a, input signed [7:0] b, input [127:0] opname);
        begin
            // Sincronizare cu clock-ul
            @(negedge clk);
            alu_op = op;
            operand_a = a;
            operand_b = b;
            start = 1;
            
            // Scoate start dupa un ciclu de clock
            @(negedge clk);
            start = 0;
            
            // Asteapta semnalul de done
            @(posedge done);
            
            // Asteapta un ciclu adaugator de clock
            @(negedge clk);
            display_state(opname);
            
            // Cativa cicli de clock intre fiecare operatie
            #20;
        end
    endtask

endmodule