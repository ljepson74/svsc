import uvm_pkg::*;
class e_test extends uvm_test;
   `uvm_component_utils(e_test)

     e_driver e_driver_inst;

   function new(string name, uvm_component parent);
      super.new(name,parent);
      $display(" %m:  Great.  We instantiated this test.");
   endfunction

   function void buile_phase(uvm_phase phase);
      super.buile_phase(phase);
      //e_env_inst = new("georgi",this);
      e_driver_inst = e_driver::type_id::create("e_driver_inst",this);
   endfunction

   function void connect_phase(uvm_phase phase);
      uvm_config_db#(virtual e_if)::get(this,"","e_driver_inst_handle", e_driver_inst.e_if_inst_ghost);
   endfunction

   task run_phase(uvm_phase phase);
      phase.raise_objection(.obj(this));
      #400ns;      
      phase.drop_objection(.obj(this));      
   endtask   
endclass : e_test
