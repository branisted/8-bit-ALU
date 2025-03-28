library verilog;
use verilog.vl_types.all;
entity mux_3to1 is
    port(
        sel_add         : in     vl_logic;
        sel_sub         : in     vl_logic;
        in_adder        : in     vl_logic_vector(7 downto 0);
        in_subtractor   : in     vl_logic_vector(7 downto 0);
        in_default      : in     vl_logic_vector(7 downto 0);
        \out\           : out    vl_logic_vector(7 downto 0)
    );
end mux_3to1;
