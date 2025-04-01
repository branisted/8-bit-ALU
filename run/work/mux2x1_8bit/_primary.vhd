library verilog;
use verilog.vl_types.all;
entity mux2x1_8bit is
    port(
        Y               : out    vl_logic_vector(7 downto 0);
        A               : in     vl_logic_vector(7 downto 0);
        B               : in     vl_logic_vector(7 downto 0);
        Sel             : in     vl_logic
    );
end mux2x1_8bit;
