// define a data object "packet" that derives from uvm_object;
// for mixed-lamguage UVM communication, this SystemVerilog object needs 
// to have the same name and same data type of member fields in the same 
// order as the corresponding SystemC class

class packet extends uvm_object;
  int    data;
  `uvm_object_utils_begin(packet)
    `uvm_field_int(data, UVM_ALL_ON)
  `uvm_object_utils_end
endclass

