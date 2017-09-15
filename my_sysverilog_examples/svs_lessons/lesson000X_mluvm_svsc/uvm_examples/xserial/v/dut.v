//---------------------------------------------------------------------------
//File name   : dut.v
//Title       : Example DUT for XSerial eVC
//Project     : XSerial eVC
//Developers  : Richard Vialls
//Created     : 09-May-2002
//Description : A simple 3 input, 3 output router
//Notes       : 
//---------------------------------------------------------------------------
//Copyright (c) 2005-20010 Cadence Design Systems, Inc. All rights reserved worldwide.
//Please refer to the terms and conditions in $IPCM_HOME.
//---------------------------------------------------------------------------
`timescale 1ns/1ns

module router (reset,
               clock,
               port_a_in_data,
               port_a_err,
               port_a_out_data,
               port_b_in_data,
               port_b_err,
               port_b_out_data,
               port_c_in_data,
               port_c_err,
               port_c_out_data);

   input reset;
   input clock;
   
   input port_a_in_data;
   output port_a_err;
   output port_a_out_data;

   input port_b_in_data;
   output port_b_err;
   output port_b_out_data;

   input port_c_in_data;
   output port_c_err;
   output port_c_out_data;

   wire   reset;
   wire   clock;
   
   wire   port_a_in_data;
   wire   port_a_err;
   wire   port_a_out_data;

   wire   port_b_in_data;
   wire   port_b_err;
   wire   port_b_out_data;

   wire   port_c_in_data;
   wire   port_c_err;
   wire   port_c_out_data;

   
 
   wire [1:0] id_a;
   assign id_a = 2'b00;

   wire [1:0] id_b;
   assign id_b = 2'b01;

   wire [1:0] id_c;
   assign id_c = 2'b10;

   wire [11:0] chan_a_data;
   wire        chan_a_valid;
   reg        chan_a_ack;
   wire        chan_a_halted;
   wire        chan_a_flow_req;
   wire        chan_a_flow_halt;
   wire        chan_a_flow_ack;

   wire [11:0] chan_b_data;
   wire        chan_b_valid;
   reg        chan_b_ack;
   wire        chan_b_halted;
   wire        chan_b_flow_req;
   wire        chan_b_flow_halt;
   wire        chan_b_flow_ack;

   wire [11:0] chan_c_data;
   wire        chan_c_valid;
   reg        chan_c_ack;
   wire        chan_c_halted;
   wire        chan_c_flow_req;
   wire        chan_c_flow_halt;
   wire        chan_c_flow_ack;

   reg [1:0]   source;
   reg [11:0]  data_bus;
   reg         data_bus_valid;
   wire        full;
   


   in_channel in_port_a(.clock(clock),
                        .reset(reset),
                        .in_data(port_a_in_data),
                        .err(port_a_err),
                        .out_data(chan_a_data),
                        .out_valid(chan_a_valid),
                        .out_ack(chan_a_ack),
                        .halted(chan_a_halted),
                        .flow_req(chan_a_flow_req),
                        .flow_halt(chan_a_flow_halt),
                        .flow_ack(chan_a_flow_ack));
   
   in_channel in_port_b(.clock(clock),
                        .reset(reset),
                        .in_data(port_b_in_data),
                        .err(port_b_err),
                        .out_data(chan_b_data),
                        .out_valid(chan_b_valid),
                        .out_ack(chan_b_ack),
                        .halted(chan_b_halted),
                        .flow_req(chan_b_flow_req),
                        .flow_halt(chan_b_flow_halt),
                        .flow_ack(chan_b_flow_ack));

   in_channel in_port_c(.clock(clock),
                        .reset(reset),
                        .in_data(port_c_in_data),
                        .err(port_c_err),
                        .out_data(chan_c_data),
                        .out_valid(chan_c_valid),
                        .out_ack(chan_c_ack),
                        .halted(chan_c_halted),
                        .flow_req(chan_c_flow_req),
                        .flow_halt(chan_c_flow_halt),
                        .flow_ack(chan_c_flow_ack));
   
  
  
  
 
 
   out_channel out_port_a(.id(id_a),
                          .clock(clock),
                          .reset(reset),
                          .source(source),
                          .in_data(data_bus),
                          .in_valid(data_bus_valid),
                          .flow_req(chan_a_flow_req),
                          .flow_halt(chan_a_flow_halt),
                          .flow_ack(chan_a_flow_ack),
                          .full(chan_a_full),
                          .halted(chan_a_halted),
                          .out_data(port_a_out_data));
   
   out_channel out_port_b(.id(id_b),
                          .clock(clock),
                          .reset(reset),
                          .source(source),
                          .in_data(data_bus),
                          .in_valid(data_bus_valid),
                          .flow_req(chan_b_flow_req),
                          .flow_halt(chan_b_flow_halt),
                          .flow_ack(chan_b_flow_ack),
                          .full(chan_b_full),
                          .halted(chan_b_halted),
                          .out_data(port_b_out_data));
      
   out_channel out_port_c(.id(id_c),
                          .clock(clock),
                          .reset(reset),
                          .source(source),
                          .in_data(data_bus),
                          .in_valid(data_bus_valid),
                          .flow_req(chan_c_flow_req),
                          .flow_halt(chan_c_flow_halt),
                          .flow_ack(chan_c_flow_ack),
                          .full(chan_c_full),
                          .halted(chan_c_halted),
                          .out_data(port_c_out_data));
   
  
   // If any of the output FIFOs are full, then we cannot guarantee
   // to be able to route a frame, so stall the router.
   assign full = chan_a_full | chan_b_full | chan_c_full;
   
   // This process is the actual router. Frames from each of the
   // input channels are merged onto a single data bus (the channels
   // are prioritised, A, B then C). Each output channel then only
   // picks off the frames that are addressed to it. 
   always@(reset or full or chan_a_valid or chan_a_data
           or chan_b_valid or chan_b_data or chan_c_valid
           or chan_c_data)
      begin
         if (reset == 1'b1)
            begin
               chan_a_ack <= 1'b0;
               chan_b_ack <= 1'b0;
               chan_c_ack <= 1'b0;
            end // if (reset == 1'b1)
         else 
            begin
               if ((chan_a_valid == 1'b1) && (full == 1'b0))
                  begin
                     source <= 2'b00;
                     data_bus = chan_a_data;
                     data_bus_valid <= 1'b1;
                     chan_a_ack <= 1'b1;
                     chan_b_ack <= 1'b0;
                     chan_c_ack <= 1'b0;
                  end // if ((chan_a_valid == 1'b1) && (full == 1'b0))
               else
                  begin
                     if ((chan_b_valid == 1'b1) && (full == 1'b0))
                        begin
                           source <= 2'b01;
                           data_bus = chan_b_data;
                           data_bus_valid <= 1'b1;
                           chan_a_ack <= 1'b0;
                           chan_b_ack <= 1'b1;
                           chan_c_ack <= 1'b0;
                        end // if ((chan_b_valid == 1'b1) && (full == 1'b0))
                     else 
                        begin
                           if ((chan_c_valid == 1'b1) && (full == 1'b0))
                              begin
                                 source <= 2'b10;
                                 data_bus = chan_c_data;
                                 data_bus_valid <= 1'b1;
                                 chan_a_ack <= 1'b0;
                                 chan_b_ack <= 1'b0;
                                 chan_c_ack <= 1'b1;
                              end // if ((chan_c_valid == 1'b1) && (full == 1'b0))
                           else
                              begin
                                 data_bus = data_bus;
                                 data_bus_valid <= 1'b0;
                                 chan_a_ack <= 1'b0;
                                 chan_b_ack <= 1'b0;
                                 chan_c_ack <= 1'b0;
                              end // else: !if((chan_c_valid == 1'b1) && (full == 1'b0))
                        end // else: !if((chan_b_valid == 1'b1) && (full == 1'b0))
                  end // else: !if((chan_a_valid == 1'b1) && (full == 1'b0))
            end // else: !if(reset == 1'b1)
      end // always@ (reset or full or chan_a_valid or chan_a_data...
endmodule // router
