library verilog;
use verilog.vl_types.all;
entity register_1bit is
    port(
        clk             : in     vl_logic;
        load            : in     vl_logic;
        \in\            : in     vl_logic;
        \out\           : out    vl_logic
    );
end register_1bit;
