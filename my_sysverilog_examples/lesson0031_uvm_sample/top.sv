package my_pkg;
import uvm_pkg::*;
`include "uvm_macros.svh"

class master_comp extends uvm_component;
   `uvm_component_utils(master_comp)

   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction : new

   task run_phase (uvm_phase phase);
      `uvm_info("MASTER", "run_phase executing", UVM_LOW);
   endtask : run_phase
endclass : master_comp

class slave_comp extends uvm_component;
   `uvm_component_utils(slave_comp)

   function new(string name, uvm_component parent);
      super.new(name,parent);
   endfunction : new

   task run_phase(uvm_phase phase);
      `uvm_info("SLAVE","run_phase: Executing.",UVM_LOW)
   endtask : run_phase
endclass : slave_comp

class simple_if_comp extends uvm_component;
   master_comp master;
   slave_comp slave;

   `uvm_component_utils(simple_if_comp)

   function new(string name, uvm_component parent);
      super.new(name,parent);
   endfunction : new

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      master = master_comp::type_id::create("master",this); 
      slave = slave_comp::type_id::create("slave",this); 
   endfunction : build_phase

   task run_phase (uvm_phase phase);
      uvm_component child, parent;
      `uvm_info("UVC","run_phase: Executing",UVM_LOW)
      parent=get_parent();
      `uvm_info("UVC",{"parent: ",parent.get_full_name()}, UVM_LOW)
      child=get_child("master");
      `uvm_info("UVC",{"child: ",child.get_name()}, UVM_LOW) 
      child=get_child("slave");
      `uvm_info("UVC",{"child: ",child.get_name()}, UVM_LOW)
   endtask : run_phase
endclass : simple_if_comp

class testbench_comp extends uvm_component;
   simple_if_comp my_uvc;

   `uvm_component_utils(testbench_comp)

   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction : new

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      my_uvc=simple_if_comp::type_id::create("my_uvc",this);
   endfunction : build_phase

   function void end_of_elaboration_phase(uvm_phase phase);
      super.end_of_elaboration_phase(phase);
      `uvm_info("TBENCH",{"end_of_elaboration_phase: Hierarchy\n",this.sprint()},UVM_LOW)
   endfunction : end_of_elaboration_phase

   task run_phase (uvm_phase phase);
      `uvm_info("TBENCH","run_phase: Executing.",UVM_LOW)
   endtask : run_phase
endclass : testbench_comp
endpackage : my_pkg


module albert;
import uvm_pkg::*;
`include "uvm_macros.svh"
import my_pkg::*;

testbench_comp testbench;

initial
begin
   $display("Hello World");
   testbench = testbench_comp::type_id::create("testbench",null);
   run_test();
end

endmodule : albert
