library verilog;
use verilog.vl_types.all;
entity booth_encoder is
    port(
        b               : in     vl_logic_vector(1 downto 0);
        A               : in     vl_logic_vector(7 downto 0);
        PP              : out    vl_logic_vector(8 downto 0)
    );
end booth_encoder;
