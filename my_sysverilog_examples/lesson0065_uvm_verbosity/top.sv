package my_pkg;
   import uvm_pkg::*;
`include "uvm_macros.svh"
   
class my_component extends uvm_component();

   function new(string name, uvm_component parent);
      super.new(name,parent);
   endfunction
endclass : my_component
endpackage


module top;
   import uvm_pkg::*;
`include "uvm_macros.svh"
   import my_pkg::*;

   uvm_verbosity smthg;
   my_component  my_comp;

   initial
     begin
	$display("****** Fun w/ UVM_VERBOSITY *******************");
	my_comp = new("fred",null);
	smthg=UVM_LOW;

	`uvm_info("TESTBENCH","run_phase: Executing.  Testbench run_phase<<<<",UVM_LOW)
	`uvm_info("TESTBENCH","UVM_VERBOSITY>=UVM_LOW",   UVM_LOW)
	`uvm_info("TESTBENCH","UVM_VERBOSITY>=UVM_MEDIUM",UVM_MEDIUM)
	`uvm_info("TESTBENCH","UVM_VERBOSITY>=UVM_HIGH",  UVM_HIGH)

	`uvm_info("TESTBENCH",$psprintf("UVM_VERBOSITY of smthg=%0p=%0d", smthg, smthg), UVM_NONE)
     end
endmodule : top
