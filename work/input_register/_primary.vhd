library verilog;
use verilog.vl_types.all;
entity input_register is
    port(
        clk             : in     vl_logic;
        reset           : in     vl_logic;
        in_data         : in     vl_logic_vector(7 downto 0);
        load            : in     vl_logic;
        out_data        : out    vl_logic_vector(7 downto 0)
    );
end input_register;
