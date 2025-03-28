library verilog;
use verilog.vl_types.all;
entity multiplier is
    port(
        clk             : in     vl_logic;
        rst             : in     vl_logic;
        start           : in     vl_logic;
        multiplier      : in     vl_logic_vector(7 downto 0);
        multiplicand    : in     vl_logic_vector(7 downto 0);
        product         : out    vl_logic_vector(15 downto 0);
        done            : out    vl_logic
    );
end multiplier;
