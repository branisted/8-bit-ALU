library verilog;
use verilog.vl_types.all;
entity adder_16bit is
    port(
        a               : in     vl_logic_vector(15 downto 0);
        b               : in     vl_logic_vector(15 downto 0);
        sum             : out    vl_logic_vector(15 downto 0);
        cout            : out    vl_logic
    );
end adder_16bit;
