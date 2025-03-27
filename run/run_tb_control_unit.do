quit -sim  # Quit the simulation, ensuring no previous simulation data is left

# empty the work library if present

if [file exists "work"] {vdel -all}

#create a new work library

vlib work

# Compile Verilog files (add more if needed)
vlog ../src/control_unit/control_unit.v
vlog ../testbenches/tb_control_unit.v

# Start the simulation
vsim tb_control_unit

# Log all signals recursively
log -r /*

# Add signals to the waveform viewer (with radix option)

add wave -radix unsigned /tb_control_unit/op_sel
add wave -radix unsigned /tb_control_unit/clk
add wave -radix unsigned /tb_control_unit/reset
add wave -radix unsigned /tb_control_unit/load_alu
add wave -radix unsigned /tb_control_unit/alu_op
add wave -radix unsigned /tb_control_unit/done

# Run the simulation for 200 ns (or adjust the time as necessary)
run 200ns

# End simulation (optional, just for completeness)
quit -sim
