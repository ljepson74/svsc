//ex: DEFINEPLUSARG(bit,"+my_bit","blahblah",1,)
// bit mybit;
// function
//
//
//

`include "iclp.svh"
import uvm_pkg::*;
`include "uvm_macros.svh"
class ru_clp extends iclp;

   string where="clp";
   int    verb =UVM_LOW;  //verbosity

   `uvm_component_utils(ru_clp)

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
   endfunction

   function new(string name="iclp", uvm_component parent = null);
      super.new(name,parent);
      `uvm_info(where,"calling new inside ru_clp",verb);
      allow_plusarg(.valtype(BIT),   .arg("+my_bit"),    .desc("1: he bit me  0: he no bit me"), .dflt(1));
      allow_plusarg(.valtype(INT),   .arg("+my_int"),    .desc("#times to print statement"), .dflt(11));
      allow_plusarg(.valtype(STRING),.arg("+my_string"), .desc("Name of possible biter"), .dflt_s("Paulie"));
   endfunction : new

endclass : ru_clp
