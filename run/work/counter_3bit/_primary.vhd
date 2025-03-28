library verilog;
use verilog.vl_types.all;
entity counter_3bit is
    port(
        clk             : in     vl_logic;
        rst             : in     vl_logic;
        en              : in     vl_logic;
        count           : out    vl_logic_vector(2 downto 0);
        done            : out    vl_logic
    );
end counter_3bit;
