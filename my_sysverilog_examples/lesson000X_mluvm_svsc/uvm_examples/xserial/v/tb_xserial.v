//--------------------------------------------------------------------------- 
//File name   : tb_xserial.v
//Title       : Verilog testbench for XSerial eVC demo
//Project     : XSerial eVC
//Developers  : Richard Vialls
//Created     : 09-May-2002
//Description : 
//Notes       : 
//--------------------------------------------------------------------------- 
//Copyright (c) 2005-20010 Cadence Design Systems, Inc. All rights reserved worldwide.
//Please refer to the terms and conditions in $IPCM_HOME.
//--------------------------------------------------------------------------- 
   
module xserial_evc_demo;
   

  
   reg reset;
   reg clock;
   reg port_a_in_data;
   wire port_a_err;
   wire port_a_out_data;
   reg port_b_in_data;
   wire port_b_err;
   wire port_b_out_data;
   reg port_c_in_data;
   wire port_c_err;
   wire port_c_out_data;

   router  router(.reset(reset),
                  .clock(clock),
                  .port_a_in_data(port_a_in_data),
                  .port_a_err(port_a_err),
                  .port_a_out_data(port_a_out_data),
                  .port_b_in_data(port_b_in_data),
                  .port_b_err(port_b_err),
                  .port_b_out_data(port_b_out_data),
                  .port_c_in_data(port_c_in_data),
                  .port_c_err(port_c_err),
                  .port_c_out_data(port_c_out_data));
 
 

  

   always
      #100 clock = ~clock;


   initial
      begin
         reset = 1'b1;
         clock = 1'b1;
         #500 reset = 1'b0;
      end // initial begin
   
endmodule // xserial_evc_demo
