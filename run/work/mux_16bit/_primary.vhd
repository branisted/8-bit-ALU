library verilog;
use verilog.vl_types.all;
entity mux_16bit is
    port(
        in0             : in     vl_logic_vector(15 downto 0);
        in1             : in     vl_logic_vector(15 downto 0);
        sel             : in     vl_logic;
        \out\           : out    vl_logic_vector(15 downto 0)
    );
end mux_16bit;
