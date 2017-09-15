import uvm_pkg::*;
`include "uvm_macros.svh"

class svs_test extends uvm_test;
   `uvm_component_utils(svs_test)
   svs_env env_u;
   function new(string name="svs_test", uvm_component parent=null);
      super.new(name,parent);
      env_u = new("env_u",this);
//    uvm_config_db#(virtual svs_if)::set(uvm_root::get(),"*","handle0",svs_top.svs_if_u[0]);
   endfunction : new

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