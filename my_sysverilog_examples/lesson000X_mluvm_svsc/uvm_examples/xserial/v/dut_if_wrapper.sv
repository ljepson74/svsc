/*------------------------------------------------------------------------- 
File name   : dut_if_wrap.sv
Title       : XSerial router wrapper (using a interface)
Project     : XSerial golden example
Developers  : 
Created     : 
Description : [Future] This file defines a module that wraps the XSerial 
            : router DUT and defines an interface port.
Notes       : 
              This file is NOT currently used by the scripts, until modport
              expressions are supported.

-------------------------------------------------------------------
Copyright (c) 2005-20010 Cadence Design Systems, Inc. All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME.
------------------------------------------------------------------- */


 
 module dut_wrap (interface dut_if);

   router dut(
	      .reset(              dut_if.reset),
              .clock(              dut_if.clock),
              .port_a_in_data(     dut_if.port_a_in_data),
              .port_a_err(         dut_if.port_a_err),
              .port_a_out_data(    dut_if.port_a_out_data),
              .port_b_in_data(     dut_if.port_b_in_data),
              .port_b_err(         dut_if.port_b_err),
              .port_b_out_data(    dut_if.port_b_out_data),
              .port_c_in_data(     dut_if.port_c_in_data),
              .port_c_err(         dut_if.port_c_err),
              .port_c_out_data(    dut_if.port_c_out_data)   );
   
endmodule : dut_wrap

