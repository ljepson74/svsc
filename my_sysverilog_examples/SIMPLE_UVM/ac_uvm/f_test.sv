import uvm_pkg::*;
class f_test extends uvm_test;
   `uvm_component_utils(f_test)

     f_driver f_driver_inst;

   function new(string name, uvm_component parent);
      super.new(name,parent);     $display(" %m: Great.  We instantiated test");
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      f_driver_inst  = f_driver::type_id::create("f_driver_inst",this);
   endfunction

   function void connect_phase(uvm_phase phase);
      uvm_config_db#(virtual f_if)::get(this,"","f_driver_inst_handle",f_driver_inst.f_if_inst_ghost);
   endfunction

   task run_phase(uvm_phase phase);
      phase.raise_objection(.obj(this));
      #400ns;
      phase.drop_objection(.obj(this));      
   endtask      

endclass : f_test // f_test
