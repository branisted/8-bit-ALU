library verilog;
use verilog.vl_types.all;
entity control_unit is
    port(
        op              : in     vl_logic_vector(1 downto 0);
        add_en          : out    vl_logic;
        sub_en          : out    vl_logic;
        mul_en          : out    vl_logic;
        div_en          : out    vl_logic
    );
end control_unit;
