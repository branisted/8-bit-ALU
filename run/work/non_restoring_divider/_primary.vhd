library verilog;
use verilog.vl_types.all;
entity non_restoring_divider is
    port(
        dividend        : in     vl_logic_vector(7 downto 0);
        divisor         : in     vl_logic_vector(7 downto 0);
        quotient        : out    vl_logic_vector(7 downto 0);
        remainder       : out    vl_logic_vector(7 downto 0)
    );
end non_restoring_divider;
