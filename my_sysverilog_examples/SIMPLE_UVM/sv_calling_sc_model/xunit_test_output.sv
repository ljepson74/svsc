// define a data object "xunit_test_output" that derives from uvm_object;


`ifndef PACKET_SV
`define PACKET_SV

class xunit_test_output extends uvm_object;
  rand int    xresult;
   
  `uvm_object_utils_begin(xunit_test_output)
    `uvm_field_int(xresult, UVM_ALL_ON)
  `uvm_object_utils_end

   function new(string name = "xunit_test_output");
      super.new(name);
   endfunction : new
 
endclass

`endif //  `ifndef PACKET_SV
