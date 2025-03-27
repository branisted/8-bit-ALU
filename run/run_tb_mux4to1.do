quit -sim  # Quit the simulation, ensuring no previous simulation data is left

# empty the work library if present
if { [file exists "work"] } { vdel -all }

# create a new work library
vlib work

# Compile Verilog files (add more if needed)
vlog ../src/mux/mux4to1.v
vlog ../testbenches/tb_mux4to1.v

# Start the simulation
vsim tb_mux4to1

# Log all signals recursively
log -r /*

# Add signals to the waveform viewer (with radix option)
add wave -radix unsigned /tb_mux4to1/data
add wave -radix unsigned /tb_mux4to1/sel
add wave -radix unsigned /tb_mux4to1/out

# Run the simulation for 200 ns (or adjust the time as necessary)
run 200ns

# End simulation (optional, just for completeness)
quit -sim
