library verilog;
use verilog.vl_types.all;
entity multiplier is
    generic(
        width           : integer := 8
    );
    port(
        A               : in     vl_logic_vector;
        B               : in     vl_logic_vector;
        Product         : out    vl_logic_vector
    );
end multiplier;
