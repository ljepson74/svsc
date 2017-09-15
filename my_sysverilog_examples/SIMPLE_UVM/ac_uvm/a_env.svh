/*
class my_env;
endclass // my_env
*/

/*
class my_env extends uvm_env;
endclass // my_env
*/

import uvm_pkg::*;   //WHY DO I NEED THIS HERE?

class a_env extends uvm_env;

   a_driver a_driver_inst;

   `uvm_component_utils(a_env)     

     
     function new(string name, uvm_component parent);
	super.new(name,parent);
     endfunction : new

   virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      a_driver_inst  = a_driver::type_id::create("a_driver_inst", this);      
   endfunction : build

   function void connect_phase(uvm_phase phase);
      if(!uvm_config_db#(virtual a_if)::get(this, "", "this_is_my_tag", a_driver_inst.a_if_inst))
	`uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"});
   endfunction : connect

endclass // a_env
