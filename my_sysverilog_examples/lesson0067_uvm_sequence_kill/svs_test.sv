import uvm_pkg::*;
`include "uvm_macros.svh"

class svs_test extends uvm_test;

   `uvm_component_utils(svs_test)

   function new(string name="svs_testasdf", uvm_component parent=null);
      super.new(name,parent);
      repeat(1) $display("Prathyusha is nice......");
   endfunction : new

   task run_phase(uvm_phase phase);
      phase.raise_objection(this);
      repeat(1) $display("David is nice......");
      phase.drop_objection(this);
   endtask : run_phase
endclass : svs_test
/*
class svs_test2 extends uvm_test;

   `uvm_component_utils(svs_test)

   function new(string name="svs_tasdfasdfestasdf", uvm_component parent=null);
      super.new(name,parent);
      repeat(1) $display("Shreyas is nice......");
   endfunction : new

   task run_phase(uvm_phase phase);
      phase.raise_objection(this);
      repeat(1) $display("Chhavi is nice......");
      phase.drop_objection(this);
   endtask : run_phase
endclass : svs_test2
*/
