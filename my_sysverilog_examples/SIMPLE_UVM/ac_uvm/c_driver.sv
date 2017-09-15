import uvm_pkg::*;

class c_driver extends uvm_driver;
   `uvm_component_utils(c_driver)

     virtual c_if c_if_inst;

   function new(string name, uvm_component parent);
      super.new(name,parent);
   endfunction

   task reset();
      c_if_inst.my_signal <= 'b0;
   endtask : reset

   task run_phase(uvm_phase phase);
      #5;
      c_if_inst.my_signal <= 'b0;
      #25;
      c_if_inst.my_signal <= 'bZ;
      #15;
      c_if_inst.my_signal <= 'b1;
      #5;
      c_if_inst.my_signal <= 'bX;
      #5;
      c_if_inst.my_signal <= 'b0;
      #25;
      c_if_inst.my_signal <= 'bZ;
      #15;
      c_if_inst.my_signal <= 'b1;
      #5;
      c_if_inst.my_signal <= 'bX;
      #5;
      c_if_inst.my_signal <= 'b0;
      #25;
      c_if_inst.my_signal <= 'bZ;
      #15;
      c_if_inst.my_signal <= 'b1;
      #5;
      c_if_inst.my_signal <= 'b0;
   endtask : run_phase

endclass: c_driver
