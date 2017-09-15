import uvm_pkg::*;
`include "uvm_macros.svh"

class svs_test extends uvm_test;
   string receiver;
   int albert;
      
   `uvm_component_utils(svs_test)
   
   function new(string name="svs_test", uvm_component parent=null);
      super.new(name,parent);
      uvm_config_db#(string)::set(uvm_root::get(),"*","my_string","linc_learns");
      uvm_config_db#(int)::set(null,null,"albert_variable",4433);
   endfunction : new

   task run_phase(uvm_phase phase);
      phase.raise_objection(this);

      void'(uvm_config_db#(string)::get(uvm_root::get(),"*","my_string",receiver));
      void'(uvm_config_db#(int)::get(null,null,"albert_variable",albert));

      repeat(3) 
	`uvm_info("DBG",$psprintf("Got: >>%0s<<>>%0d<<",receiver,albert),UVM_NONE)
      
      phase.drop_objection(this);
   endtask : run_phase
endclass : svs_test