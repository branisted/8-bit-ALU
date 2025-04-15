library verilog;
use verilog.vl_types.all;
entity alu_control is
    port(
        clk             : in     vl_logic;
        reset           : in     vl_logic;
        start           : in     vl_logic;
        opcode          : in     vl_logic_vector(2 downto 0);
        mul_done        : in     vl_logic;
        div_done        : in     vl_logic;
        load_a          : out    vl_logic;
        load_b          : out    vl_logic;
        load_out        : out    vl_logic;
        done            : out    vl_logic;
        start_add       : out    vl_logic;
        start_sub       : out    vl_logic;
        start_mul       : out    vl_logic;
        start_div       : out    vl_logic;
        start_and       : out    vl_logic;
        start_or        : out    vl_logic;
        start_xor       : out    vl_logic;
        sel_op          : out    vl_logic_vector(2 downto 0)
    );
end alu_control;
