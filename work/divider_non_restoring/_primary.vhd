library verilog;
use verilog.vl_types.all;
entity divider_non_restoring is
    port(
        dividend        : in     vl_logic_vector(15 downto 0);
        divisor         : in     vl_logic_vector(7 downto 0);
        quotient        : out    vl_logic_vector(7 downto 0);
        remainder       : out    vl_logic_vector(7 downto 0)
    );
end divider_non_restoring;
