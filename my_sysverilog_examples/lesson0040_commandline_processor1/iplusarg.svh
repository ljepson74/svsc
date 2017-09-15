
`include "iclp_pkg.svh"
`include "uvm_macros.svh"
import iclp_pkg::*;
class plusarg;
   string where="+arg";
   int    verb =UVM_HIGH;

  //plusargs are bit(a boolean), an int, or a string
//   typedef enum {BIT=0, INT=1, STRING=2} valuetype_e;  //this is now defined twice
 
   string       name;
   string       desc;
   valuetype_e  type_of;
   int          value_i;
   int          value_i_default;
   string       value_s;
   string       value_s_default;
 
   function new();
   endfunction

   extern function show(input string note="");
endclass : plusarg


function plusarg::show(input string note="");
   string msg="";

   msg = "name:%0s.  type:%0d. ";
   if (type_of==2) begin //string
      msg = {msg, $psprintf("default:%0s  now:%0s",value_s_default, value_s)};
   end else begin
      msg = {msg, $psprintf("default:%0d  now:%0d",value_i_default, value_i)};
   end

   `uvm_info(where,$psprintf("%0s",msg),verb)
endfunction : show
