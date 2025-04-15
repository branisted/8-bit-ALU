library verilog;
use verilog.vl_types.all;
entity alu_mul is
    port(
        clk             : in     vl_logic;
        start           : in     vl_logic;
        a               : in     vl_logic_vector(7 downto 0);
        b               : in     vl_logic_vector(7 downto 0);
        product         : out    vl_logic_vector(15 downto 0);
        done            : out    vl_logic
    );
end alu_mul;
