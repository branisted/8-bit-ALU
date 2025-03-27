library verilog;
use verilog.vl_types.all;
entity control_unit is
    port(
        op_sel          : in     vl_logic_vector(1 downto 0);
        clk             : in     vl_logic;
        reset           : in     vl_logic;
        load_alu        : out    vl_logic;
        alu_op          : out    vl_logic_vector(1 downto 0);
        done            : out    vl_logic
    );
end control_unit;
