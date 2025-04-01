library verilog;
use verilog.vl_types.all;
entity gp_logic is
    port(
        A               : in     vl_logic;
        B               : in     vl_logic;
        G               : out    vl_logic;
        P               : out    vl_logic
    );
end gp_logic;
