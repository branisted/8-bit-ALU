library verilog;
use verilog.vl_types.all;
entity inverter_8bit is
    port(
        B               : in     vl_logic_vector(7 downto 0);
        B_inv           : out    vl_logic_vector(7 downto 0)
    );
end inverter_8bit;
