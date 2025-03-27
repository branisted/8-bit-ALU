quit -sim  # Quit the simulation, ensuring no previous simulation data is left

# empty the work library if present

if [file exists "work"] {vdel -all}

#create a new work library

vlib work

# Compile Verilog files (add more if needed)
vlog ../src/arithmetic_unit/adder.v
vlog ../testbenches/tb_adder.v

# Start the simulation
vsim tb_adder

# Log all signals recursively
log -r /*

# Add signals to the waveform viewer (with radix option)
add wave -radix unsigned /tb_adder/A
add wave -radix unsigned /tb_adder/B
add wave -radix unsigned /tb_adder/Cin
add wave -radix unsigned /tb_adder/Sum
add wave -radix unsigned /tb_adder/Cout

# Run the simulation for 200 ns (or adjust the time as necessary)
run 200ns

# End simulation (optional, just for completeness)
quit -sim
