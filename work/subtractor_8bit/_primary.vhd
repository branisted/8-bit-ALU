library verilog;
use verilog.vl_types.all;
entity subtractor_8bit is
    port(
        A               : in     vl_logic_vector(7 downto 0);
        B               : in     vl_logic_vector(7 downto 0);
        Diff            : out    vl_logic_vector(7 downto 0);
        Cout            : out    vl_logic
    );
end subtractor_8bit;
