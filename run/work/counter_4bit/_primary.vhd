library verilog;
use verilog.vl_types.all;
entity counter_4bit is
    port(
        clk             : in     vl_logic;
        load            : in     vl_logic;
        dec             : in     vl_logic;
        \in\            : in     vl_logic_vector(3 downto 0);
        \out\           : out    vl_logic_vector(3 downto 0)
    );
end counter_4bit;
