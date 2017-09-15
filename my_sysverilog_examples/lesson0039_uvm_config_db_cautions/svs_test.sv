import uvm_pkg::*;
`include "uvm_macros.svh"

class svs_test extends uvm_test;
   `uvm_component_utils(svs_test)

   int stupid = 123;
      
   function new(string name="svs_test", uvm_component parent=null);
      super.new(name,parent);
   endfunction : new

   function void build_phase(uvm_phase phase);

      uvm_config_db#(int)::set(uvm_root::get(),"*","handle11",1066);
      
      if (!uvm_config_db#(int)::get(uvm_root::get(),"*","handle11",stupid)) begin
	 `uvm_fatal("CONFIG",$psprintf("---ee--"))
      end
      
      $display(" stupid=%d",stupid);
   endfunction : build_phase

   function void end_of_elaboration_phase(uvm_phase phase);
      uvm_top.print_topology();
   endfunction

   task run_phase(uvm_phase phase);
      phase.raise_objection(this);
      repeat (4) `uvm_info("DBG","message1 goes here",UVM_NONE)
      #100;
      phase.drop_objection(this);
   endtask : run_phase
endclass : svs_test
