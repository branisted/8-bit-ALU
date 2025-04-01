library verilog;
use verilog.vl_types.all;
entity booth_encoder is
    port(
        triplet         : in     vl_logic_vector(2 downto 0);
        sel             : out    vl_logic_vector(2 downto 0)
    );
end booth_encoder;
