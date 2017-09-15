//--------------------------------------------------------------------------- 
//File name   : tb_xcore.v
//Title       : Verilog testbench for XCore demo
//Project     : XCore eVC
//Developers  : Richard Vialls, Black Cat Electronics Ltd
//Created     : 22-May-2002
//Description : 
//Notes       : 
//--------------------------------------------------------------------------- 
//Copyright (c) 2002-2010 Cadence Design Systems,Inc.All rights reserved worldwide
//(Acquired from Verisity Design,Inc.,2005).
//Please refer to the terms and conditions in $IPCM_HOME

//---------------------------------------------------------------------------
`timescale 1ns/1ns
module xcore_tb;

     
   
   // XBus signals
   reg xbus_clock;
   reg xbus_reset;
   reg xbus_start;
   reg [15:0] xbus_addr;
   reg [1:0] xbus_size;
   reg xbus_read;
   reg xbus_write;
   reg xbus_bip;
   wire [7:0] xbus_data;
   wire xbus_wait;
   wire xbus_error;
   reg xbus_grant;
   reg xbus_request; 

   // XSerial signals
   reg xserial_tx_clock;
   wire xserial_tx_data;
   reg xserial_rx_clock;
   reg xserial_rx_data;

   // XCore signals
   reg [15:8] base_addr;
   
   
   always
      #5 xbus_clock = ~xbus_clock;
   
   
   always
      #10 xserial_tx_clock  = ~xserial_tx_clock;
   
   
   initial
      begin
         xbus_clock = 1'b1;    
         xserial_tx_clock = 1'b1;
         xbus_reset = 1'b1;
         base_addr[15:8] = 8'b00000000;
         #100 xbus_reset = 1'b0; 
      end
   
   
   xcore xcore(.base_addr(base_addr),
               .xbus_clock(xbus_clock),
               .xbus_reset(xbus_reset),
               .xbus_start(xbus_start),
               .xbus_request(xbus_request),
               .xbus_grant(xbus_grant),
               .xbus_addr(xbus_addr),
               .xbus_size(xbus_size),
               .xbus_read(xbus_read),
               .xbus_write(xbus_write),
               .xbus_bip(xbus_bip),
               .xbus_data(xbus_data),
               .xbus_wait(xbus_wait),
               .xbus_error(xbus_error),
               .xserial_rx_clock(xserial_rx_clock),
               .xserial_rx_data(xserial_rx_data),
               .xserial_tx_clock(xserial_tx_clock),
               .xserial_tx_data(xserial_tx_data));
   
endmodule // xcore_tb

