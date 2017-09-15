// Use -nocopyright -and -reduce_messages so that results will 
// match .au file no matter what version
-NOCOPYRIGHT
-reduce_messages

// redirect ncsim output to ncsim.log
-log_ncsim ncsim.log

// specify the SV test top as -uvmtop argument
-uvmtop SV:test
  
// specify the SC testbench top as static top
-sctop tbtop
  
// specify that sysc is in the design
-sysc

// specify SystemC testbench src file
tbtop.cpp

// specify SystemVerilog test src file
test.sv

