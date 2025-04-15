library verilog;
use verilog.vl_types.all;
entity alu_top is
    port(
        clk             : in     vl_logic;
        reset           : in     vl_logic;
        start           : in     vl_logic;
        op              : in     vl_logic_vector(2 downto 0);
        in_a            : in     vl_logic_vector(7 downto 0);
        in_b            : in     vl_logic_vector(7 downto 0);
        result          : out    vl_logic_vector(15 downto 0);
        done            : out    vl_logic
    );
end alu_top;
