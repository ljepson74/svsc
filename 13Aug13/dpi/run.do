vlib work

vlog -sv tb.sv
gcc -m32 -c -fPIC -I/home/altera/altera-bin/12.1/modelsim_ase/include c_code.c
gcc -m32 -shared -Bsymbolic -o c_code.so c_code.o

vsim -c -sv_lib c_code tb

run -all
quit -f

