library verilog;
use verilog.vl_types.all;
entity alu_8bit is
    port(
        clk             : in     vl_logic;
        reset           : in     vl_logic;
        A               : in     vl_logic_vector(7 downto 0);
        B               : in     vl_logic_vector(7 downto 0);
        op_sel          : in     vl_logic_vector(1 downto 0);
        load            : in     vl_logic;
        result          : out    vl_logic_vector(15 downto 0);
        done            : out    vl_logic
    );
end alu_8bit;
