//---------------------------------------------------------------------------
//File name   : in_chan.v
//Title       : Example DUT for XSerial eVC - input channel and fifo
//Project     : XSerial eVC
//Developers  : Richard Vialls
//Created     : 09-May-2002
//Description : Input deserialiser and FIFO for 1 input channel of routerC
//Notes       : 
//---------------------------------------------------------------------------
//Copyright (c) 2005-20010 Cadence Design Systems, Inc. All rights reserved worldwide.
//Please refer to the terms and conditions in $IPCM_HOME.
//---------------------------------------------------------------------------

module in_channel(clock,
                  reset,
                  in_data,
                  err,
                  out_data,
                  out_valid,
                  out_ack,
                  halted,
                  flow_req,
                  flow_halt,
                  flow_ack);
   input clock;
   input reset;
   input in_data;
   output err;
   output [11:0] out_data;
   output        out_valid;
   input         out_ack;
   output        halted;
   output        flow_req;
   output        flow_halt;
   input         flow_ack;
   
   
   wire          clock;
   wire          reset;
   wire          in_data;
   reg           err;
   wire [11:0]   out_data;
   
   reg           out_valid;
   wire          out_ack;
   reg           halted;
   wire          flow_req;
   wire          flow_halt;
   wire          flow_ack;
   
   // This is the input channel FIFO
   reg [11:0]    fifo [0:3] ;
      
   // collect_count counts the bits of the frame as it is collected
   reg [3:0]     collect_count;
   
   // input frame is latched in following signal
   reg [12:0]    collector;
  
   // temporary signal for parity calculation
   reg           parity;
   
   // in_valid is high for the clock cycle in which collector contains valid data
   reg           in_valid;

   // FIFO write pointer
   reg [1:0]     write_ptr;
  
   // FIFO read pointer
   reg [1:0]     read_ptr;
  
   // Counts current number of items in FIFO
   reg [2:0]     item_count;
  
   // High causes write to FIFO
   reg           write_fifo;
  
   // High causes read from FIFO
   wire          read_fifo;
  
   // Local copy of flow_req
   reg           flow_req_int;
  
   // Local copy of flow_halt
   reg           flow_halt_int;


   // This process calculates parity on the incoming frame (which should be
   // even).
   always@(posedge clock)
      begin
         if (collect_count == 4'b1101)
            begin
               parity <= in_data;
            end // if (collect_count == 4'b1101)
         else
            begin
               parity <= parity ^ in_data;
            end // else: !if(collect_count != 4'b1101)
      end // always@ (posedge clock)
   
  
   // This process determines when collector contains a valid frame. 
   always@(posedge clock)
      begin
         if (reset == 1'b1)
            begin
               in_valid <= 1'b0;
            end // if (reset == 1'b1)
         else
            begin
               if (collect_count == 4'b0001)
                  begin
                     in_valid <= 1'b1;
                  end // if (collect_count == 4'b0001)
               else
                  begin
                     in_valid <= 1'b0;
                  end // else: !if(collect_count == 4'b0001)
            end // else: !if(reset == 1'b1)
      end // always@ (posedge clock)


   assign out_data = fifo[read_ptr];
   


   

  
   // This process counts the incoming bits from the port
   always@(posedge clock)
      begin
         if (reset == 1'b1)
            begin
               collect_count <= 4'b0000;
            end // if reset
         else
            begin
               if (collect_count == 4'b0000)
                  begin
                     if (in_data == 1'b0)
                        begin
                           collect_count <= 4'b1101;
                        end // if in_data
                  end // if (collect_count == 4'b0000)
               else
                  begin
                     collect_count <= collect_count - 1;
                  end // else: !if(collect_count == 4'b0000)
            end // else: !if(reset == 1'b1)
      end // always@ (posedge clock)
   
  
   // This process collects the incoming frame
   always@(posedge clock)
      begin
         if (collect_count != 4'b0000)
            begin
               collector[11:0] <= collector[12:1];
               collector[12] <= in_data;
            end // if (collect_count != 4'b0000)
      end // always@ (posedge clock)
      
  
   // This process drives the err signal if a parity error is detected.
   always@(posedge clock)
      begin
         if (reset == 1'b1)
            begin
               err <= 0;
            end // if (reset == 1'b1)
         else
            begin
               if (in_valid == 1'b1)
                  begin
                     err <= parity;
                  end // if (in_valid == 1'b1)
            end // else: !if(reset == 1'b1)
      end // always@ (posedge clock)
   
         
   // This process writes non-message frames to the FIFO.
   always@(in_valid or parity or collector)
      begin
         if ((in_valid == 1'b1) && (parity == 1'b0) && (collector[3:2] != 2'b01))
            begin
               write_fifo <= 1'b1;
            end // if ((in_valid == 1'b1) && (parity == 1'b0) && (collector[3:2] != 2'b01))
         else
            begin
               write_fifo <= 1'b0;
            end // else: !if((in_valid == 1'b1) && (parity == 1'b0) && (collector[3:2] != 2'b01))
      end // always@ (in_valid or parity or collector)
   
   // This process processes HALT and RESUME messages and drives halted to the
   // rest of the system.
   always@(posedge clock)
      begin
         if (reset == 1'b1)
            begin
               halted <= 1'b0;
            end // if (reset == 1'b1)
         else
            begin
               if ((in_valid == 1'b1) && (parity == 1'b0) && (collector[11:2] == 10'b0000000101))
                  begin
                     halted <= 1'b1;
                  end // if ((in_valid == 1'b1) && (parity == 1'b0) && (collector[11:2] == 10'b0000000101))
               else
                  begin
                     if ((in_valid == 1'b1) && (parity == 1'b0) && (collector[11:2] == 10'b0000001001))
                        begin
                           halted <= 1'b0;
                        end // if ((in_valid == 1'b1) && (parity == 1'b0) && (collector[11:2] == 10'b0000001001))
                  end // else: !if((in_valid == 1'b1) && (parity == 1'b0) && (collector[11:2] == 10'b0000000101))
            end // else: !if(reset == 1'b1)
      end // always@ (posedge clock)
   
    
   // This process handles the write pointer for the FIFO
   always@(posedge clock)
      begin
         if (reset == 1'b1)
            begin
               write_ptr <= 2'b00;
            end // if (reset == 1'b1)
         else
            if (write_fifo == 1'b1)
               begin
                  fifo[write_ptr] = collector[11:0];
                  write_ptr <= write_ptr +1;
               end // if (write_fifo == 1'b1)
      end // always@ (posedge clock)
   
    
   // The FIFO is read each time the out_ack signal is asserted.
   assign read_fifo = out_ack;
  
   // This process handles the read pointer for the FIFO
   always@(posedge clock)
      begin
         if (reset == 1'b1)
            begin
               read_ptr <= 2'b00;
            end // if (reset == 1'b1)
         else
            begin
               if (read_fifo == 1'b1)
                  begin
                     read_ptr <= read_ptr + 1;
                  end // if (read_fifo == 1'b1)
            end // else: !if(reset == 1'b1)
      end // always@ (posedge clock)
   

   // This process keeps track of how many items are currently in the FIFO.
   always@(posedge clock)
      begin
         if(reset == 1'b1)
            begin
               item_count <= 3'b000;
            end // if (reset == 1'b1)
         else
            begin
               if ((write_fifo == 1'b1) && (read_fifo == 1'b0))
                  begin
                     item_count <= item_count +1;
                  end // if ((write_fifo == 1'b1) && (read_fifo == 1'b0))
               else
                  begin
                     if ((write_fifo == 1'b0) && (read_fifo == 1'b1))
                        begin
                           item_count <= item_count - 1;
                        end // if ((write_fifo == 1'b0) && (read_fifo == 1'b1))
                  end // else: !if((write_fifo == 1'b1) && (read_fifo == 1'b0))
            end // else: !if(reset == 1'b1)
      end // always@ (posedge clock)

   
   // This process determines when the FIFO contains valid data that
   // can be routed to an output channel.
   always@(reset or item_count)
      begin
         if (reset == 1'b1)
            begin
               out_valid <= 1'b0;
            end // if (reset == 1'b1)
         else
            begin
               if (item_count != 3'b000)
                  begin
                     out_valid <= 1'b1;
                  end // if (item_count != 0)
               else
                  begin
                     out_valid <= 1'b0;
                  end // else: !if(item_count != 3'b000)
            end // else: !if(reset == 1'b1)
      end // always@ (reset or item_count)

  
       
   // This process determines when there is a possibility that the input
   // FIFO could overflow and generates requests for flow control messages
   // to prevent this. Note that after a flow control HALT message is sent,
   // up to two frames may be received before the remote end of the link
   // can stop sending more frames.
   
   always@(posedge clock)
      begin
         if (reset == 1'b1)
            begin
               flow_req_int <= 1'b0;
               flow_halt_int <= 1'b0;
            end // if (reset == 1'b1)
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
                     if ((write_fifo == 1'b0) && (read_fifo == 1'b1) && (item_count == 3'b010))
                        begin
                           if ((flow_req_int == 1'b1) && (flow_halt_int == 1'b1) && (flow_ack == 1'b0))
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
                           if (flow_ack == 1'b1)
                              begin
                                 flow_req_int <= 1'b0;
                              end // if (flow_ack == 1'b1)
                        end // else: !if((write_fifo == 1'b0) && (read_fifo == 1'b1) && (item_count == 3'b010))
                  end // else: !if((write_fifo == 1'b1) && (read_fifo == 1'b0) && (item_count == 3'b001))
            end // else: !if(reset == 1'b1)
      end // always@ (posedge clock)
   
   assign flow_req = flow_req_int;
   assign flow_halt = flow_halt_int;
endmodule // in_channel

