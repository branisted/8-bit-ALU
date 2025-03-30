library verilog;
use verilog.vl_types.all;
entity multiplier is
    port(
        A               : in     vl_logic_vector(7 downto 0);
        B               : in     vl_logic_vector(7 downto 0);
        result          : out    vl_logic_vector(15 downto 0)
    );
end multiplier;
