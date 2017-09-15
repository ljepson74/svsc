import uvm_pkg::*;

class a_configuration extends uvm_object;
   `uvm_object_utils(a_configuration)

     function new(string name = "");
	super.new(name);
     endfunction
   
endclass // a_configuration


