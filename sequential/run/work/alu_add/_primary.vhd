library verilog;
use verilog.vl_types.all;
entity alu_add is
    port(
        clk             : in     vl_logic;
        a               : in     vl_logic_vector(7 downto 0);
        b               : in     vl_logic_vector(7 downto 0);
        start           : in     vl_logic;
        sum             : out    vl_logic_vector(15 downto 0)
    );
end alu_add;
