quit -sim  # Quit the simulation, ensuring no previous simulation data is left

# empty the work library if present
if { [file exists "work"] } { vdel -all }

# create a new work library
vlib work

# Compile Verilog files (add more if needed)
vlog ../src/registers/input_register.v
vlog ../testbenches/tb_register.v

# Start the simulation
vsim tb_register

# Log all signals recursively
log -r /*

# Add signals to the waveform viewer (with radix option)
add wave -radix unsigned /tb_register/clk
add wave -radix unsigned /tb_register/reset
add wave -radix unsigned /tb_register/in_data
add wave -radix unsigned /tb_register/load
add wave -radix unsigned /tb_register/out_data

# Run the simulation for 200 ns (or adjust the time as necessary)
run 200ns

# End simulation (optional, just for completeness)
quit -sim
