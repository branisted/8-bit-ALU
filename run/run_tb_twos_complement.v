quit -sim  # Quit the simulation, ensuring no previous simulation data is left

# empty the work library if present

if [file exists "work"] {vdel -all}

#create a new work library

vlib work

# Compile Verilog files (add more if needed)
vlog ../src/other/twos_complement.v
vlog ../src/other/full_adder.v
vlog ../testbenches/tb_twos_complement.v

vsim tb_twos_complement

run -all

quit -sim