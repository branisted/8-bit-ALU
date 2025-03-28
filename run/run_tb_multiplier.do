quit -sim  # Quit the simulation, ensuring no previous simulation data is left

# empty the work library if present

if [file exists "work"] {vdel -all}

#create a new work library

vlib work

# Compile Verilog files (add more if needed)
vlog ../src/arithmetic_unit/multiplier.v
vlog ../testbenches/tb_multiplier.v

vsim tb_multiplier

log -r /*

add wave -radix unsigned /tb_multiplier/clk
add wave -radix unsigned /tb_multiplier/rst
add wave -radix unsigned /tb_multiplier/multiplier
add wave -radix unsigned /tb_multiplier/multiplicand
add wave -radix unsigned /tb_multiplier/product

run -all

quit -sim