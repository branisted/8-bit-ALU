library verilog;
use verilog.vl_types.all;
entity regn is
    generic(
        N               : integer := 8
    );
    port(
        clk             : in     vl_logic;
        en              : in     vl_logic;
        d               : in     vl_logic_vector;
        q               : out    vl_logic_vector
    );
end regn;
