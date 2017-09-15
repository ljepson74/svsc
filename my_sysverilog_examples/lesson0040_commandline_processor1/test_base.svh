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
      clp=ru_clp::type_id::create("clp",this);
      `uvm_info(where,"***BUILD***.",UVM_HIGH)
   endfunction : build_phase
   
   task run_phase(uvm_phase phase);
      `uvm_info(where,"raise obj",UVM_HIGH)
      phase.raise_objection(this);
      
      `uvm_info(where,$psprintf("***RUN***. #%0d times",clp.i("my_int")),UVM_HIGH)

      // Check the variables here
      repeat(clp.my_int) `uvm_info(where,$psprintf("WE HAVE: my_bit:%0d  my_int:%0d  my_integer=%0d  my_string=%0s",
						   clp.my_bit,clp.my_int,clp.my_integer,clp.my_string),UVM_HIGH)

      `uvm_info(where,"drop obj",UVM_HIGH)
      phase.drop_objection(this);
   endtask : run_phase
endclass : test_base
