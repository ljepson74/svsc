import uvm_pkg::*;

class d_test extends uvm_test;
   `uvm_component_utils(d_test)
   
   d_driver d_driver_inst;

   function new(string name, uvm_component parent);      
      super.new(name,parent);      
      $display(" %m:  Great.  We instantiated this test.");
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);      
      d_driver_inst  = new();
   endfunction

   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);      
      uvm_config_db#(virtual d_if)::get(this,"","d_if_inst_handle",d_driver_inst.d_if_ghost); 
   endfunction


   task run_phase(uvm_phase phase);
      phase.raise_objection(.obj(this));
      d_driver_inst.run();
      phase.drop_objection(.obj(this));
   endtask

endclass : d_test
