library verilog;
use verilog.vl_types.all;
entity carry_lookahead_unit is
    port(
        G               : in     vl_logic_vector(3 downto 0);
        P               : in     vl_logic_vector(3 downto 0);
        Cin             : in     vl_logic;
        C               : out    vl_logic_vector(3 downto 0);
        Cout            : out    vl_logic
    );
end carry_lookahead_unit;
