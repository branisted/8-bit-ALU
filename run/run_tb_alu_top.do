quit -sim  # Quit the simulation, ensuring no previous simulation data is left

# empty the work library if present
if { [file exists "work"] } { vdel -all }

#create a new work library
vlib work

# Compile Verilog files
vlog ../src/arithmetic_unit/adder.v
vlog ../src/other/*.v
vlog ../src/arithmetic_unit/divider.v
vlog ../src/arithmetic_unit/multiplier.v
vlog ../src/arithmetic_unit/subtractor.v
vlog ../src/control_unit/control_unit.v
vlog ../src/control_unit/arithmetic_unit.v
vlog ../src/alu_top.v

# Compile the testbench
vlog ../testbenches/tb_alu_top.v

# Start the simulation
vsim tb_alu_top

# Log all signals recursively
log -r /*

# Add signals to the waveform viewer

# Run the simulation for 200 ns
run -all

# End simulation
quit -sim
