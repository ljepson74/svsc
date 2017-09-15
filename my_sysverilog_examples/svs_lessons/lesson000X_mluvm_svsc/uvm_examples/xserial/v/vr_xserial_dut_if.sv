/*-------------------------------------------------------------------------
File name   : xserial_dut_if.sv
Title       : DUT interface declarations for the XSerial router
Project     : Xserial uVC
Created     : 2006-02-23
Description : [Future] This file declares the DUT interface for the router DUT
Notes       : 
            : 
              This file is NOT currently used by the scripts, until modport
              expressions are supported.
 
----------------------------------------------------------------------
Copyright (c) 2005-20010 Cadence Design Systems, Inc. \
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME.
----------------------------------------------------------------------*/



interface xserial_dut_if ( input logic clock, input logic reset);

   logic port_a_in_data;
   logic port_a_err;
   logic port_a_out_data;
   
   logic port_b_in_data;
   logic port_b_err;
   logic port_b_out_data;
   
   logic port_c_in_data;
   logic port_c_err;
   logic port_c_out_data;

   
   modport port_a (
	       input   .xserial_reset(reset),
	       input   .xserial_rx_clock(clock),
               input   .xserial_rx_data(port_a_in_data),
	       input   .xserial_tx_clock(clock),
               output  .xserial_tx_data(port_a_out_data),
               output  .xserial_err(port_a_err) );


   modport port_b ( 
	       input   .xserial_reset(reset),
	       input   .xserial_rx_clock(clock),
               input   .xserial_rx_data(port_b_in_data),
	       input   .xserial_tx_clock(clock),
               output  .xserial_tx_data(port_b_out_data),
               output  .xserial_err(port_b_err));

   modport port_c ( 
	       input   .xserial_reset(reset),
	       input   .xserial_rx_clock(clock),
               input   .xserial_rx_data(port_b_in_data),
	       input   .xserial_tx_clock(clock),
               output  .xserial_tx_data(port_b_out_data),
               output  .xserial_err(port_b_err));

   modport monitor(
	        input   clock,
	        input   reset,
		input  port_a_in_data,
                input  port_a_err,
                input  port_a_out_data,
                input  port_b_in_data,
                input  port_b_err,
                input  port_b_out_data,
                input  port_c_in_data,
                input  port_c_err,
                input  port_c_out_data);
   
   
endinterface 


