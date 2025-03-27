vlib work

vlog ../src/arithmetic_unit/subtractor.v
vlog tb_subtractor.v

vsim tb_subtractor

log -r /*

add wave -radix unsigned /tb_subtractor/A
add wave -radix unsigned /tb_subtractor/B
add wave -radix unsigned /tb_subtractor/Diff
add wave -radix unsigned /tb_subtractor/Cout

run 100ns

quit