# Makefile for compiling and simulating the 8-bit ALU
SIMULATOR = iverilog

all: compile simulate

compile:
	$(SIMULATOR) -o alu_sim src/*.v testbenches/tb_alu_top.v

simulate:
	vvp alu_sim