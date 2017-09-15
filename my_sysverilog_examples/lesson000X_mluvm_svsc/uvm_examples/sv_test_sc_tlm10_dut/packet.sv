// define a data object "packet" that derives from uvm_object;
// for ML UVM communication, this SV class needs to have the same name
// and same data type of member fields in the same order as the
// corresponding SC class

class packet extends uvm_object;
  int    data;
  `uvm_object_utils_begin(packet)
    `uvm_field_int(data, UVM_ALL_ON)
  `uvm_object_utils_end

  function void next();
    static int d = 101;
    data = d++;
  endfunction

  function int get_data();
    return data;
  endfunction

endclass

