library verilog;
use verilog.vl_types.all;
entity alu_or is
    port(
        clk             : in     vl_logic;
        a               : in     vl_logic_vector(7 downto 0);
        b               : in     vl_logic_vector(7 downto 0);
        start           : in     vl_logic;
        res             : out    vl_logic_vector(15 downto 0)
    );
end alu_or;
