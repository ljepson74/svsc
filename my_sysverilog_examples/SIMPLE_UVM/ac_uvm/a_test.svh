import uvm_pkg::*;

class a_test extends uvm_test;
   `uvm_component_utils(a_test)

     a_env a_env_inst;

     function new(string name, uvm_component parent);
	super.new(name,parent);
     endfunction // new

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      begin
	 a_configuration a_configuration_inst;
	 
	 a_configuration_inst  = new;

	 uvm_config_db#(a_configuration)::set
	   (.cntxt(this), .inst_name("*"), .field_name("config"), .value(a_configuration_inst));

	 a_env_inst  = a_env::type_id::create(.name("a_env_inst"), .parent(this));

      end
   endfunction

   task run_phase(uvm_phase phase);
      phase.raise_objection(.obj(this));
      `uvm_info(" my little simple test", $psprintf("WE ARE IN HERE, HEY.")  , UVM_LOW)
      #100ns;
      phase.drop_objection(.obj(this));      
      
   endtask: run_phase   
   
endclass // a_test

