// Set up env variable CDS_INST_DIR to point to the root of the IUS install

// Use -nocopyright -and -reduce_messages so that results will 
// match .au file no matter what version
-NOCOPYRIGHT
-reduce_messages

// redirect ncsim output to ncsim.log
-log_ncsim ncsim.log

// specify the SV test top as -uvmtop argument
-uvmtop SV:svtest
  
// specify the SC test top as -uvmtop argument
-uvmtop SC:sctest
  
// specify that sysc is in the design
-sysc
  
// specify the name of the top Verilog module and snapshot
-top topmodule

// specify SystemC test src file
test.cpp

// specify SystemVerilog test src file
test.sv

