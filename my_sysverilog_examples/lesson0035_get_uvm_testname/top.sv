import uvm_pkg::*;
`include "uvm_macros.svh"

class my_test;// extends uvm_test;


   function new();
      $display(" WE ARE IN HERE " );
      `uvm_info("WE ARE ALSO"," IN OVER HERE------->>>>>-->>>>",UVM_LOW)
   endfunction

/*
   function new(string name="my_test",uvm_component parent = null);
      super.new(name,parent);
      `uvm_info("DEBUG","MADE A NEW ONE",UVM_HIGH)
   endfunction : new
 */ 
endclass : my_test


module top;

   my_test my_test;
   
   initial begin
      my_test=new();
   end

endmodule