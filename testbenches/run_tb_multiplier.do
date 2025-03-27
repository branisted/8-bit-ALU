vlib work

vlog ../src/arithmetic_unit/multiplier_booth_radix4.v
vlog tb_multiplier.v

vsim tb_multiplier

log -r /*

add wave -radix unsigned /tb_multiplier/A
add wave -radix unsigned /tb_multiplier/B
add wave -radix unsigned /tb_multiplier/Product

run 200ns

quit