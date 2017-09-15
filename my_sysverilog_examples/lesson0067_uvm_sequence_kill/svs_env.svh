import uvm_pkg::*;
`include "uvm_macros.svh"

class svs_env extends uvm_env;
   `uvm_component_utils(svs_env)

   function new(string name="svs_env", uvm_component parent=null);
      super.new(name,parent);
   endfunction : new

   function void build_phase(uvm_phase phase);

   endfunction : build_phase

endclass : svs_env
