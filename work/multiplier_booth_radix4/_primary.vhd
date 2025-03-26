library verilog;
use verilog.vl_types.all;
entity multiplier_booth_radix4 is
    port(
        A               : in     vl_logic_vector(7 downto 0);
        B               : in     vl_logic_vector(7 downto 0);
        Product         : out    vl_logic_vector(15 downto 0)
    );
end multiplier_booth_radix4;
