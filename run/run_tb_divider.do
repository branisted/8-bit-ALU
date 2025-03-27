quit -sim  # Quit the simulation, ensuring no previous simulation data is left

# empty the work library if present

if [file exists "work"] {vdel -all}

#create a new work library

vlib work

# Compile Verilog files (add more if needed)
vlog ../src/arithmetic_unit/divider.v
vlog ../testbenches/tb_divider.v

vsim tb_divider

log -r /*

add wave -radix unsigned /tb_divider/A
add wave -radix unsigned /tb_divider/B
add wave -radix unsigned /tb_divider/quotient
add wave -radix unsigned /tb_divider/remainder

run 200ns

quit -sim