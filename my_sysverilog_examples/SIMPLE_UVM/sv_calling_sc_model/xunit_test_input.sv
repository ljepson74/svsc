class xunit_test_input extends uvm_object;
   rand int xstimulus;

   `uvm_object_utils_begin(xunit_test_input)
     `uvm_field_int(xstimulus, UVM_ALL_ON)
   `uvm_object_utils_end

     function new(string name="xunit_test_input");
	super.new(name);
     endfunction : new

endclass // xunit_test_input

