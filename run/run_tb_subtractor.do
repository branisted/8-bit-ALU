quit -sim  # Quit the simulation, ensuring no previous simulation data is left

# empty the work library if present

if [file exists "work"] {vdel -all}

#create a new work library

vlib work

# Compile Verilog files (add more if needed)
vlog ../src/arithmetic_unit/adder.v
vlog ../src/other/*.v
vlog ../src/arithmetic_unit/subtractor.v
vlog ../testbenches/tb_subtractor.v

vsim tb_subtractor

log -r /*

add wave -radix unsigned /tb_subtractor/A
add wave -radix unsigned /tb_subtractor/B
add wave -radix unsigned /tb_subtractor/Diff
add wave -radix unsigned /tb_subtractor/Borrow

run 250ns

quit -sim