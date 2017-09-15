import uvm_pkg::*;

class c_env extends uvm_env;

   c_driver c_driver_inst;
   `uvm_component_utils(c_env)

     function new(string name, uvm_component parent);
	super.new(name,parent);
     endfunction

   virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      c_driver_inst = c_driver::type_id::create("c_driver_inst_huh",this);
   endfunction : build_phase

   function void connect_phase(uvm_phase phase);
      if(!uvm_config_db#(virtual c_if)::get(this,"","c_driver_inst",c_driver_inst.c_if_inst))
	`uvm_fatal("NOVIF",{"virtual interface is not set for this, senor: ", get_full_name(), ".vif"});
   endfunction

endclass // a_env
