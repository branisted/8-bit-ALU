library verilog;
use verilog.vl_types.all;
entity alu_top is
    port(
        A               : in     vl_logic_vector(7 downto 0);
        B               : in     vl_logic_vector(7 downto 0);
        op              : in     vl_logic_vector(1 downto 0);
        result          : out    vl_logic_vector(15 downto 0)
    );
end alu_top;
