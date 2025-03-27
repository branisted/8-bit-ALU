library verilog;
use verilog.vl_types.all;
entity subtractor is
    port(
        A               : in     vl_logic_vector(7 downto 0);
        B               : in     vl_logic_vector(7 downto 0);
        Diff            : out    vl_logic_vector(7 downto 0);
        Borrow          : out    vl_logic
    );
end subtractor;
