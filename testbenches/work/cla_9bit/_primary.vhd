library verilog;
use verilog.vl_types.all;
entity cla_9bit is
    port(
        A               : in     vl_logic_vector(8 downto 0);
        B               : in     vl_logic_vector(8 downto 0);
        Cin             : in     vl_logic;
        Sum             : out    vl_logic_vector(8 downto 0);
        Cout            : out    vl_logic
    );
end cla_9bit;
