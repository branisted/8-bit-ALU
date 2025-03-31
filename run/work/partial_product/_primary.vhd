library verilog;
use verilog.vl_types.all;
entity partial_product is
    port(
        A               : in     vl_logic_vector(7 downto 0);
        sel             : in     vl_logic_vector(2 downto 0);
        pp              : out    vl_logic_vector(15 downto 0)
    );
end partial_product;
