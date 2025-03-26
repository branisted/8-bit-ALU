library verilog;
use verilog.vl_types.all;
entity Subtractor is
    port(
        a               : in     vl_logic_vector(15 downto 0);
        b               : in     vl_logic_vector(7 downto 0);
        diff            : out    vl_logic_vector(15 downto 0);
        borrow          : out    vl_logic
    );
end Subtractor;
