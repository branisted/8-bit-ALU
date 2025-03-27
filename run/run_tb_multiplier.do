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

add wave -radix unsigned /tb_multiplier/A
add wave -radix unsigned /tb_multiplier/B
add wave -radix unsigned /tb_multiplier/Product

run 200ns

quit -sim