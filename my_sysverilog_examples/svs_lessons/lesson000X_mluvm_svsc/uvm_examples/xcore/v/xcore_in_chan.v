/*--------------------------------------------------------------------------- 
File name   : xcore_in_chan.v
Title       : XCore input channel
Project     : XCore SystemVerilog Methodology
Developers  : Richard Vialls
Created     : 2002-05-21
Description : This block provides an XSerial receiver and input FIFO for
            : XCore.
            :
            : Input frames are collected and checked for parity. Message
            : frames are processed to extract HALT/RESUME information and
            : then discarded. All other frames are queued in a FIFO ready
            : for reading from the XBus interface. Only the frame payload
            : and parity error status are queued in the FIFO, the start
            : bit, stop bit and parity bit are discarded.
            :
            : Central to the design is the fact that the xserial_rx_clock
            : has no relation to the xbus_clock. This means that clock
            : domain crossing must be correctly implemented so as to 
            : avoid metastability. This can be easily achieved because the
            : rate at which frames arrive is significantly slower than the
            : speed of the XBus clock. As each frame arrives, it is latched
            : in the rx_frame signal and the rx_frame_valid signal changes
            : state. This signal is then double clocked into the XBus clock
            : domain to remove metastability and is used to write the frame
            : to the FIFO.
Notes       : The xserial_rx_clock should not be higher nominal frequency
            : than the xbus_clock.
---------------------------------------------------------------------------
Copyright (c) 2002-2010 Cadence Design Systems,Inc.All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME

---------------------------------------------------------------------------*/

`timescale 1ns/1ns

module xcore_in_chan(xbus_clock,
                     xbus_reset,
                     frame,
                     frame_valid,
                     read_fifo,
                     halted,
                     flow_req,
                     flow_halt,
                     flow_ack,
                     xserial_rx_clock,
                     xserial_rx_data);
   
   input    xbus_clock;
   input    xbus_reset;
   output [12:0] frame;
   output        frame_valid;
   input    read_fifo;
   output   halted;
   output   flow_req;
   output   flow_halt;
   input    flow_ack;
   
   // xserial signals
   input    xserial_rx_clock;
   input    xserial_rx_data;
   
   wire     xbus_clock;
   wire     xbus_reset;
   wire [12:0] frame;
   reg         frame_valid;
   wire        read_fifo;
   reg         halted;
   wire        flow_req;
   wire        flow_halt;
   wire        flow_ack;
   
   // xserial signals
   wire        xserial_rx_clock;
   wire        xserial_rx_data;
   
   
   
   reg [3:0]   collect_count;
   reg [12:0]  collector;
   reg         collector_valid;
   reg         parity;
   reg [12:0]  rx_frame;
   reg         rx_frame_valid;
   reg         rx_frame_valid_c;
   reg         rx_frame_valid_cc;
   reg         rx_frame_valid_ccc;
   wire        xbus_frame_valid;
   
   
   
   reg [12:0]  fifo [0:3];
   reg         write_fifo;
   reg [1:0]   write_ptr;
   reg [1:0]   read_ptr;
   reg [2:0]   item_count;
   reg         flow_req_int;
   reg         flow_halt_int;

`ifdef XCORE_SIM   

// cover FIFO overflow indication
 cover_fifo_overflow : cover property (@(posedge xbus_clock) (write_fifo == 1'b1 |-> ##1 item_count < 3'b100 ));

//Transaction creation for rx_frame   
  trview_rx_frame: cover property (@(posedge xbus_clock) ( ((collect_count == 4'b0000 && xserial_rx_data == 1'b0) ##[1:$] $rose(collector_valid))));
 

//coverage for frame_kind : data, message ( halt ,  resume , idle)
//message frame
  cover_rx_mode_message_frame : cover property (@(posedge xbus_clock) (xbus_frame_valid && rx_frame[12] == 1'b0  && rx_frame[3:2] == 2'b01));

//halt frame
  cover_rx_mode_halt_frame : cover property (@(posedge xbus_clock) (xbus_frame_valid && rx_frame[12] == 1'b0  && rx_frame[4:2] == 3'b101));

//resume frame
  cover_rx_mode_resume_frame : cover property (@(posedge xbus_clock) (xbus_frame_valid && rx_frame[12] == 1'b0  && rx_frame[4:2] == 3'b001));

//data frame
  cover_rx_mode_data_frame : cover property (@(posedge xbus_clock) (xbus_frame_valid && rx_frame[12] == 1'b0  && rx_frame[3:2] == 2'b00));

`endif
   
   // This process counts the incoming bits from the XSerial RX port
   always @(posedge xserial_rx_clock)
      begin
         if(xbus_reset == 1'b1)
            begin
               collect_count <= 4'b0000;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if (collect_count == 4'b0000)
                  begin
                     if (xserial_rx_data == 1'b0)
                        begin
                           collect_count <= 4'b1101;
                        end // if (xserial_rx_data == 1'b0)
                  end // if (collect_count == 4'b0000)
               else
                  begin
                     collect_count <= collect_count - 4'b0001;
                  end // else: !if(collect_count == 4'b0000)
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xserial_rx_clock)
  

   
   // This process collects the incoming frame
   always@(posedge xserial_rx_clock)
      begin
         if (collect_count != 4'b0000)
            begin
               collector[11:0] <= collector[12:1];
               collector[12] <= xserial_rx_data;
            end // if (collect_count != 4'b0000)
      end // always@ (posedge xserial_rx_clock)
   
   
   // This process calculates parity on the incoming frame (which should be
   // even).
   always@(posedge xserial_rx_clock)
      begin
         if (collect_count == 4'b1101)
            begin
               parity <= xserial_rx_data;
            end // if (collect_count == 4'b1101)
         else
            begin
               parity <= parity ^ xserial_rx_data;
            end // else: !if(collect_count == 4'b1101)
      end // always@ (posedge xserial_rx_clock)
   
   
   // This process determines when collector contains a valid frame. 
   always@(posedge xserial_rx_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               collector_valid <= 1'b0;
            end // if (collector_reset == 1'b1)
         else
            begin
               if(collect_count == 4'b0001)
                  begin
                     collector_valid <= 1'b1;
                  end // if (collect_count == 4'b0001)
               else
                  begin
                     collector_valid <= 1'b0;
                  end // else: !if(collect_count == 4'b0001)
            end // else: !if(collector_reset == 1'b1)
      end // always@ (posedge xserial_rx_clock)
   
    
   // This process clocks the collected frame into the frame signal. Note that
   // the 13 bits that are latched are the 12 bit payload plus 1 bit that
   // indicates whether the incoming frame had a parity error (1) or not (0).
   always@(posedge xserial_rx_clock)
      begin
         if(collector_valid == 1'b1)
            begin
               rx_frame <= {parity,collector[11:0]};
            end // if (collector_valid == 1'b1)
      end // always@ (posedge xserial_rx_clock)
   
   
   // This process signals to the XBus clock domain when the frame signal
   // contains a valid frame. Each valid frame is signalled by a change of
   // state of the rx_frame_valid signal.
   always@(posedge xserial_rx_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               rx_frame_valid <= 1'b0;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if (collector_valid == 1'b1)
                  begin
                     rx_frame_valid <= ~rx_frame_valid;
                  end // if (collector_valid == 1'b1)
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xserial_rx_clock)
   
   
   // This process double clocks the rx_frame_valid signal into the XBus clock
   // domain. An version with an additional clock cycle delay is also produced
   // to assist in detecting changes in this signal.
   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               rx_frame_valid_c <= 1'b0;
               rx_frame_valid_cc <= 1'b0;
               rx_frame_valid_ccc <= 1'b0;
            end // if (xbus_reset == 1'b1)
         else
            begin
               rx_frame_valid_c <= rx_frame_valid;
               rx_frame_valid_cc <= rx_frame_valid_c;
               rx_frame_valid_ccc <= rx_frame_valid_cc;
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)
   
           
   
   // This signal is high whenever there is a change on rx_frame_valid_cc
   assign xbus_frame_valid = rx_frame_valid_cc ^ rx_frame_valid_ccc;
   
   
   // This process handles received HALT and RESUME messages and drives the
   // halted signal to the TX path.
   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               halted <= 1'b0;
            end // if (xbus_reset == 1'b1)
         else
            begin                                       
              if((xbus_frame_valid == 1'b1) 
                 && (rx_frame[12] == 1'b0)  // Not bad parity
                 && (rx_frame[4:2] == 3'b101)) // HALT MESSAGE frame
                 
                  begin
                     halted <= 1'b1;
                  end // if ((xbus_frame_valid == 1'b1) && (rx_frame == 13'b0000000000101))
               else
                  begin
                    if( (xbus_frame_valid == 1'b1) 
                        &&  (rx_frame[12] == 1'b0)  // Not bad parity
                        && (rx_frame[4:2] == 3'b001)) // RESUME MESSAGE frame
                      begin
                           halted <= 1'b0;
                        end // if ((xbus_frame_valid == 1'b1) && (rx_frame == 13'b0000000001001))
                  end // else: !if((xbus_frame_valid == 1'b1) && (rx_frame == 13'b0000000000101))
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)
   
                  
   
   // This process determines when a non-message frame has been received and
   // needs to be written to the FIFO.
   always@(xbus_frame_valid or rx_frame)
      begin
         if ((xbus_frame_valid == 1'b1) && (rx_frame[3:2] != 2'b01))
            begin
               write_fifo <= 1'b1;
            end // if ((xbus_frame_valid == 1'b1) && (rx_frame[3:2] != 2'b01))
         else
            begin
               write_fifo <= 1'b0;
            end // else: !if((xbus_frame_valid == 1'b1) && (rx_frame[3:2] != 2'b01))
      end // always@ (xbus_fram_valid or rx_frame)
   
   
   // This process handles the write side of the FIFO. 
   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               write_ptr <= 2'b00;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if (write_fifo == 1'b1)
                  begin
                     fifo[write_ptr] = rx_frame;
                     write_ptr <= write_ptr + 2'b01;
                  end // if (write_fifo == 1'b1)
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)
   
                     
   
   // The output of this block is the next item in the FIFO
   assign  frame = fifo[read_ptr];
   
   // This process handles the read pointer for the FIFO
   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               read_ptr <= 2'b00;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if ((read_fifo == 1'b1) && (read_ptr != write_ptr))
                  begin
                     read_ptr <= read_ptr + 2'b01;
                  end // if (read_fifo == 1'b1)
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)
   
   
   
  
 
   // This process keeps track of how many items are currently in the FIFO.
   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               item_count <= 3'b000;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if ((write_fifo == 1'b1) && (read_fifo == 1'b0))
                  begin
                     item_count <= item_count + 3'b001;
                  end // if ((write_fifo == 1'b1) && (read_fifo == 1'b0))
               else
                  begin
                     if((write_fifo == 1'b0)&&(read_fifo == 1'b1) && (item_count > 3'b000))
                        begin
                           item_count <= item_count - 3'b001;
                        end // if ((write_fifo == 1'b0)&&(read_fifo == 1'b1))
                  end // else: !if((write_fifo == 1'b1) && (read_fifo == 1'b0))
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)
   
   
   
   // This process determines whether the FIFO has valid data in it or not.
   always@(item_count)
      begin
         if (item_count == 3'b000)
            begin
               frame_valid <= 1'b0;
            end // if (item_count == 4'b0000)
         else
            begin
               frame_valid <= 1'b1;
            end // else: !if(item_count == 4'b0000)
      end // always@ (item_count)
   
         
    
   // This process determines when there is a possibility that the
   // FIFO could overflow and generates requests for flow control messages
   // to prevent this. Note that after a flow control HALT message is sent,
   // up to two frames may be received before the remote end of the link
   // can stop sending more frames.
   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               flow_req_int <= 1'b0;
               flow_halt_int <= 1'b0;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if ((write_fifo == 1'b1) && (read_fifo == 1'b0) && (item_count == 3'b001))
                  begin
                     if ((flow_req_int == 1'b1) && (flow_halt_int == 1'b0) && (flow_ack == 1'b0))
                        begin
                           flow_req_int <= 1'b0;
                        end // if ((flow_req_int == 1'b1) && (flow_halt_int == 1'b0) && (flow_ack == 1'b0))
                     else
                        begin
                           flow_req_int <= 1'b1;
                           flow_halt_int <= 1'b1;
                        end // else: !if((flow_req_int == 1'b1) && (flow_halt_int == 1'b0) && (flow_ack == 1'b0))
                  end // if ((write_fifo == 1'b1) && (read_fifo == 1'b0) && (item_count == 3'b001))
               else
                  begin
                     if ((write_fifo == 1'b1) && (read_fifo == 1'b0) && (item_count == 3'b001))
                        begin
                           if((flow_req_int == 1'b1) && (flow_halt_int == 1'b0) && (flow_ack == 1'b0))
                              begin
                                 flow_req_int <= 1'b0;
                              end // if ((flow_req_int == 1'b1) && (flow_halt_int == 1'b0) && (flow_ack == 1'b0))
                           else
                              begin
                                 flow_req_int <= 1'b1;
                                 flow_halt_int <= 1'b1;
                              end // else: !if((flow_req_int == 1'b1) && (flow_halt_int == 1'b0) && (flow_ack == 1'b0))
                        end // if ((write_fifo == 1'b1) && (read_fifo == 1'b0) && (item_count == 3'b001))
                     else
                        begin
                           if ((write_fifo == 1'b0) && (read_fifo == 1'b1) && (item_count == 3'b010))
                              begin
                                 if((flow_req_int == 1'b1) && (flow_halt_int == 1'b1) && (flow_ack == 1'b0))
                                    begin
                                       flow_req_int <= 1'b0;
                                    end // if ((flow_req_int == 1'b1) && (flow_halt_int == 1'b1) && (flow_ack == 1'b0))
                                 else
                                    begin
                                       flow_req_int <= 1'b1;
                                       flow_halt_int <= 1'b0;
                                    end // else: !if((flow_req_int == 1'b1) && (flow_halt_int == 1'b1) && (flow_ack == 1'b0))
                              end // if ((write_fifo == 1'b0) && (read_fifo == 1'b1) && (item_count == 3'b010))
                           else
                              begin
                                 if(flow_ack == 1'b1)
                                    begin
                                       flow_req_int <= 1'b0;
                                    end // if (flow_ack == 1'b1)
                              end // else: !if((write_fifo == 1'b0) && (read_fifo == 1'b1) && (item_count == 3'b010))
                        end // else: !if((write_fifo == 1'b1) && (read_fifo == 1'b0) && (item_count == 3'b001))
                  end // else: !if((write_fifo == 1'b1) && (read_fifo == 1'b0) && (item_count == 3'b001))
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)
   
   assign flow_req = flow_req_int;
   assign flow_halt = flow_halt_int;
endmodule // xcore_in_chan

