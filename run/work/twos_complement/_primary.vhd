library verilog;
use verilog.vl_types.all;
entity twos_complement is
    port(
        \out\           : out    vl_logic_vector(7 downto 0);
        \in\            : in     vl_logic_vector(7 downto 0)
    );
end twos_complement;
