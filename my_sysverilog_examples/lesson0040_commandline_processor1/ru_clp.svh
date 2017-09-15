
`include "iclp.svh"
 import uvm_pkg::*;
 `include "uvm_macros.svh"

 class ru_clp extends iclp;
   `uvm_component_utils(ru_clp)
    string where="clp";
    int    verb =UVM_LOW;  //verbosity

    int    my_int;
    string my_string;

    
    function new(string name="ru_clp", uvm_component parent = null);
       super.new(name,parent);
    endfunction : new
 
   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      my_int    =add_plusarg_int(   "+my_int",    "#times INT it",    22);
      my_string =add_plusarg_string("+my_string", "Name of possible biter", "Paulie");
   endfunction : connect_phase

endclass : ru_clp
