import uvm_pkg::*;

class c_test extends uvm_test;
   `uvm_component_utils(c_test)

     c_env c_env_inst;

   function new(string name, uvm_component parent);
      super.new(name,parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build();
   
      c_env_inst = c_env::type_id::create(.name("c_env_inst"),.parent(this));
   endfunction

   task run_phase(uvm_phase phase);
      phase.raise_objection(.obj(this));

	$display(" WHAT UP AT THE FRONT?");
      `uvm_info(" smthg at start",$psprintf("STARTTERR"), UVM_LOW)
      #500ns;
      `uvm_info(" smthg at end",$psprintf("ENNNDDDERR"), UVM_LOW)
	$display(" WHAT UP AT THE BACK?");
	phase.drop_objection(.obj(this));
   endtask

endclass : c_test
