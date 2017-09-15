`include "ru_clp.svh"
import uvm_pkg::*;
`include "uvm_macros.svh"
class test_base extends uvm_test;
   string where="test_base";

   `uvm_component_utils(test_base)

   ru_clp clp;

   function new(string name="test_base", uvm_component parent=null);
      super.new(name,parent);
   endfunction : new

   function void build_phase(uvm_phase phase);
//      `uvm_info(where,"raise obj - build",UVM_HIGH)
//      phase.raise_objection(this);

      clp=ru_clp::type_id::create("clp",this);
      `uvm_info(where,"***BUILD***.",UVM_HIGH)
//      clp=new();

//      `uvm_info(where,"drop obj - build",UVM_HIGH)
//      phase.drop_objection(this);
   endfunction : build_phase
   
   task run_phase(uvm_phase phase);
      `uvm_info(where,"raise obj",UVM_HIGH)
      phase.raise_objection(this);
      
      `uvm_info(where,$psprintf("***RUN***. #%0d times",clp.i("my_int")),UVM_HIGH)

      //
      // Check the variables here
      //
      repeat(clp.i("my_int")) begin
	 `uvm_info(where,$psprintf("%0s, bit me?  T/F=%0b",clp.s("my_string"),clp.b("my_bit")),UVM_HIGH)
      end

      `uvm_info(where,"drop obj",UVM_HIGH)
      phase.drop_objection(this);
   endtask : run_phase

endclass : test_base
