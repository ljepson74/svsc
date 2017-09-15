package my_pkg;
   import uvm_pkg::*;
`include "uvm_macros.svh"

class apple extends uvm_component;
   `uvm_component_utils(apple)
   function new(string name, uvm_component parent);
      super.new(name,parent);
   endfunction : new
   task run_phase (uvm_phase phase);
      `uvm_info("UVC","run_phase: Executing.   Apple run_phase<<<",UVM_LOW)
    endtask : run_phase
endclass : apple
class orange extends apple;
   `uvm_component_utils(orange)
   function new(string name, uvm_component parent);
      super.new(name,parent);
   endfunction : new
   task run_phase (uvm_phase phase);
      `uvm_info("UVC","run_phase: Executing.   Orange run_phase<<<<",UVM_LOW)
   endtask : run_phase
endclass : orange

class my_testbench extends uvm_component;
   apple my_uvc;
   `uvm_component_utils(my_testbench)

   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction : new
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      apple::type_id::set_type_override(orange::get_type()); //Replace apple with orange
      my_uvc=apple::type_id::create("my_uvc",this);
   endfunction : build_phase

   task run_phase (uvm_phase phase);
      //my_uvc=apple::type_id::create("my_uvc",this);  //**1 cannot create a component in run phase
      `uvm_info("TESTBENCH","run_phase: Executing.  Testbench run_phase<<<<",UVM_LOW)      
   endtask : run_phase
endclass : my_testbench
endpackage : my_pkg


module top;
   import uvm_pkg::*;
`include "uvm_macros.svh"
   import my_pkg::*;

   my_testbench testbench;

   initial
     begin
	$display("******Start of Sim w/ the kids*******************");
	testbench = my_testbench::type_id::create("testbench",null);
	run_test();
     end
endmodule : top
