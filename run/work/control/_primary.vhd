library verilog;
use verilog.vl_types.all;
entity control is
    port(
        Q0              : in     vl_logic;
        Q_minus_1       : in     vl_logic;
        add             : out    vl_logic;
        sub             : out    vl_logic
    );
end control;
