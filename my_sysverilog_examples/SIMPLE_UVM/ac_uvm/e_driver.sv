import uvm_pkg::*;

class e_driver extends uvm_driver;
   `uvm_component_utils(e_driver)

     virtual e_if e_if_inst_ghost;

   function new(string name, uvm_component parent);
      super.new(name,parent);
      $display(" %m:  Great. Instantiated this driver.");
   endfunction

  task run_phase(uvm_phase phase);
     #14;
     e_if_inst_ghost.interface_bus  = 4'b10ZX;
     $display(" %m: we are really running now");
     #14;     
     e_if_inst_ghost.interface_bus  = 4'b101X;
     $display(" %m: we are really running now");
     #14;     
     e_if_inst_ghost.interface_bus  = 4'b0ZZ0;
     $display(" %m: we are really running now");
   endtask

 endclass : e_driver
