vlib work

vlog ../src/arithmetic_unit/adder.v
vlog tb_adder.v

vsim tb_adder

log -r /*

add wave -radix unsigned /tb_adder/A
add wave -radix unsigned /tb_adder/B
add wave -radix unsigned /tb_adder/Cin
add wave -radix unsigned /tb_adder/Sum
add wave -radix unsigned /tb_adder/Cout

run 100ns

quit