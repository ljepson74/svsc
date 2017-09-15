//Based upon example from A Practical Guide to Adopting the Universal Verification Methodolody (UVM)  Second Edition
//by Kathleen A Meade and Sharon Rosenberg

module my_test;  
import uvm_pkg::*;
`include "uvm_macros.svh"

   uvm_callbacks_objection hb_obj=new("hb_obj");
   
//
class child_component extends uvm_component;
   int num_hb=0;
   
   `uvm_component_utils_begin(child_component)
      `uvm_field_int(num_hb,UVM_DEFAULT)
   `uvm_component_utils_end

   function new(string name, uvm_component parent);
      super.new(name,parent);
      `uvm_info("CHILD_COMPONENT"," CREATION",UVM_LOW)
   endfunction

   virtual task run_phase(uvm_phase phase);
      `uvm_info("HBS",$sformatf("####: NUM HB: %0d", num_hb), UVM_LOW);
      for (int i=0; i<num_hb; i++) begin
	 #90 hb_obj.raise_objection(this);
      end
   endtask : run_phase
endclass : child_component


//
class parent_component extends uvm_agent;
   child_component child_0, child_1, child_2;

   `uvm_component_utils(parent_component)
   function new(string name, uvm_component parent);
      super.new(name,parent);
   endfunction : new

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      child_0 = child_component::type_id::create("child_0",this);
      child_1 = child_component::type_id::create("child_1",this);
      child_2 = child_component::type_id::create("child_2",this);

    endfunction : build_phase
endclass : parent_component


class simple_test extends uvm_test;
   parent_component parent_0;
   // Declare the heartbeat event and component
   uvm_event      hb_e;
   uvm_heartbeat  my_heartbeat;
   
   `uvm_component_utils(simple_test)

   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction : new

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      uvm_config_int::set(this, "parent_0.child_0", "num_hb", 3);
      uvm_config_int::set(this, "parent_0.child_1", "num_hb", 5);
      uvm_config_int::set(this, "parent_0.child_2", "num_hb", 2);
      parent_0 = parent_component::type_id::create("parent_0",this);
      my_heartbeat = new("my_heartbeat", this, hb_obj);
      hb_e         = new("hb_e");
   endfunction : build_phase


   function void connect_phase(uvm_phase phase);
      uvm_component hb_l[$];
      super.connect_phase(phase);
      // Set the mode: UVM_ALL_ACTIVE, UVM_ANY_ACTIVE or UVM_ONE_ACTIVE
      void'(my_heartbeat.set_mode(UVM_ANY_ACTIVE));
      // Add each component to the heartbeat component list
      my_heartbeat.add(parent.child_0);
      my_heartbeat.add(parent.child_1);
      my_heartbeat.add(parent.child_2);
      
   endfunction : connect


   virtual task run_phase(uvm_phase phase);
      this.print();
      phase.raise_objection(this, "Raising in the test");
      repeat (10) begin #100 hb_e.trigger; end
      phase.drop_objection(this, "Dropping in the test");
   endtask : run_phase
   
endclass : simple_test   


initial begin
   run_test("simple_test");
end

endmodule