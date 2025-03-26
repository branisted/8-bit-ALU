library verilog;
use verilog.vl_types.all;
entity Shifter is
    port(
        dividend        : in     vl_logic_vector(15 downto 0);
        divisor         : in     vl_logic_vector(7 downto 0);
        shift           : in     vl_logic;
        q               : out    vl_logic_vector(15 downto 0);
        r               : out    vl_logic_vector(15 downto 0)
    );
end Shifter;
