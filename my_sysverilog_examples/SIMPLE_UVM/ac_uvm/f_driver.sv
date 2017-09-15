import uvm_pkg::*;
class f_driver extends uvm_driver;
   `uvm_component_utils(f_driver)

   virtual f_if f_if_inst_ghost;

   function new(string name, uvm_component parent);
      super.new(name, parent); $display(" %m: Great.Instantiated driver"); 
   endfunction

   task run_phase(uvm_phase phase);
      #14;
      f_if_inst_ghost.interface_bus  = 4'b10ZX;      
      $display(" %m: we are really running now");      
      #14;
      f_if_inst_ghost.interface_bus  = 4'b1111;      
      $display(" %m: we are really running now");      
      #14;
      f_if_inst_ghost.interface_bus  = 4'bz0z0;      
      $display(" %m: we are really running now");            
   endtask
endclass : f_driver
