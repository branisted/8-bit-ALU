library verilog;
use verilog.vl_types.all;
entity subtractor_8bit is
    port(
        a               : in     vl_logic_vector(7 downto 0);
        b               : in     vl_logic_vector(7 downto 0);
        diff            : out    vl_logic_vector(7 downto 0)
    );
end subtractor_8bit;
