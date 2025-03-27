library verilog;
use verilog.vl_types.all;
entity output_register is
    port(
        clk             : in     vl_logic;
        reset           : in     vl_logic;
        in_data         : in     vl_logic_vector(15 downto 0);
        load            : in     vl_logic;
        out_data        : out    vl_logic_vector(15 downto 0)
    );
end output_register;
