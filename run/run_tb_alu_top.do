quit -sim  # Quit the simulation, ensuring no previous simulation data is left

# empty the work library if present

if [file exists "work"] {vdel -all}

#create a new work library

vlib work

# Compile Verilog files (add more if needed)
vlog ../src/alu_top.v
vlog ../src/arithmetic/*.v
vlog ../src/control/*.v
vlog ../src/logical/*.v
vlog ../src/other/*.v
vlog ../testbenches/tb_alu_top.v

# Start the simulation
vsim tb_alu_top

# Add all signals in the testbench and its submodules to the waveform window
# add wave -r *

# Optionally, add specific signals for clarity (uncomment if desired)
add wave tb_alu_top/clk
add wave tb_alu_top/rst
add wave tb_alu_top/start
add wave tb_alu_top/alu_op
add wave tb_alu_top/operand_a
add wave tb_alu_top/operand_b
add wave tb_alu_top/done
add wave tb_alu_top/result

# Run the simulation for 200 ns (or adjust the time as necessary)
run -all

# End simulation (optional, just for completeness)
quit -sim
