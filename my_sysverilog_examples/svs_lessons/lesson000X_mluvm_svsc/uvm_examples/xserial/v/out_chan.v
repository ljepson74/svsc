//--------------------------------------------------------------------------- 
//File name   : out_chan.v
//Title       : Example DUT for XSerial eVC - output channel and fifo
//Project     : XSerial eVC
//Developers  : Richard Vialls
//Created     : 09-May-2002
//Description : FIFO and output serialiser for 1 output channel of router
//Notes       : 
//--------------------------------------------------------------------------- 
//Copyright (c) 2005-20010 Cadence Design Systems, Inc. All rights reserved worldwide.
//Please refer to the terms and conditions in $IPCM_HOME.
//---------------------------------------------------------------------------

module out_channel(id,
                   clock,
                   reset,
                   source,
                   in_data,
                   in_valid,
                   flow_req,
                   flow_halt,
                   flow_ack,
                   full,
                   halted,
                   out_data);

   input [1:0] id;
   input       clock;
   input       reset;
   input [1:0] source;
   input [11:0] in_data;
   input        in_valid;
   input        flow_req;
   input        flow_halt;
   output       flow_ack;
   output       full;
   input        halted;
   output       out_data;
   
   wire [1:0]   id;
   wire         clock;
   wire         reset;
   wire [1:0]   source;
   wire [11:0]  in_data;
   wire         in_valid;
   wire         flow_req;
   wire         flow_halt;
   wire         flow_ack;
   reg          full;
   wire         halted;
   reg          out_data;
   
   
   
   // The output channel FIFO
   reg [11:0]   fifo [0:3];
   
   // The FIFO write pointer
   reg [1:0]    write_ptr;
   
   // The FIFO read pointer
   reg [1:0]    read_ptr;
   
   
   // Indicates how many items there are at present in the FIFO
   reg [2:0]    item_count;
   
   
   // High to cause a write to the FIFO
   reg          write_fifo;
   
   // High to cause a read from the FIFO
   reg          read_fifo;
   
   // Counts bits sent to the port
   reg [3:0]    drive_count;
   
   
   // Output shift register
   reg [14:0]   out_shift;
   
   
   // High to load a flow control message into the shift register
   reg          flow;
   
   
   // temporary signal for parity calculation
   reg          parity;
   
   
   

   
   // This process determines when a frame needs to be added to the FIFO
   
   always@(id or in_data or in_valid)
      begin
         if ((in_valid == 1'b1) && (in_data[1:0] == id))
            begin
               write_fifo <= 1'b1;
            end // if ((in_valid == 1'b1) && (in_data[1:0] == id))
         else
            begin
               write_fifo <= 1'b0;
            end // else: !if((in_valid == 1'b1) && (in_data[1:0] == id))
      end // always@ (id or in_data or in_valid)
   
   
   // This process handles the FIFO write pointer. Note that the destination
   // bits in the frame payload are replaced with the number of the channel
   // that the frame was received from (source).
   
   always@(posedge clock)
      begin
         if (reset == 1'b1)
            begin
               write_ptr <= 2'b00;
            end // if (reset == 1'b1)
         else
            begin
               //if (write_fifo == 1'b1)
               if ((in_valid == 1'b1) && (in_data[1:0] == id))
                  begin
                     fifo[write_ptr] = {in_data[11:2],source};
                     write_ptr <= write_ptr +1;
                  end // if (write_fifo == 1'b1)
            end // else: !if(reset == 1'b1)
      end // always@ (posedge clock)
   
   
   
   // This process handles the FIFO read pointer
   
   
   // This process keeps track of how many items are in the FIFO
   always@(posedge clock)
      begin
         if (reset == 1'b1)
            begin
               item_count <= 3'b000;
            end // if (reset == 1'b1)
         else
            begin
               if((write_fifo == 1'b1) && (read_fifo == 1'b0))
                  begin
                     item_count <= item_count + 1;
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
   
   
   // This process determines when the FIFO is full
   always@(item_count)
      begin
         if (item_count == 3'b100)
            begin
               full <= 1'b1;
            end // if (item_count == 3'b100)
         else
            begin
               full <= 1'b0;
            end // else: !if(item_count == 3'b100)
      end // always@ (item_count)
   
   
   // This process determines when we can read an item from the FIFO and
   // send it to the serialiser. The serialiser must be ready for another
   // frame, the FIFO must not be empty, the remote end of the link must
   // not have sent a HALT message and we mustn't be pre-empted by a
   // request to send a flow control message.
   
   always@(drive_count or item_count or halted or flow_req)
      begin
         if(( drive_count == 4'b0000 ) && (item_count != 3'b000) && (halted == 1'b0) && (flow_req == 1'b0))
            begin
               read_fifo <= 1'b1;
            end // if (( drive_count == 4'b0000 ) && (item_count != 3'b000) && (halted == 1'b0) && (flow_req == 1'b0))
         else
            begin
               read_fifo <= 1'b0;
            end // else: !if(( drive_count == 4'b0000 ) && (item_count != 3'b000) && (halted == 1'b0) && (flow_req == 1'b0))
      end // always@ (drive_count or item_count or halted or flow_req)
   
   
   // This process determines when we need to send a flow control message.
   // These take priority over all other frames.
   
   always@(drive_count or flow_req)
      begin
         if ((drive_count == 4'b0000) && (flow_req == 1'b1))
            begin
               flow <= 1'b1;
            end // if ((drive_count == 4'b0000) && (flow_req == 1'b1))
         else
            begin
               flow <= 1'b0;
            end // else: !if((drive_count == 4'b0000) && (flow_req == 1'b1))
      end // always@ (drive_count or flow_req)
   
   
   // Make sure we acknowledge that the flow control message has been sent.
   assign flow_ack = flow;
   
   // This process counts the bits of the frame as they are serialised.
   always@(posedge clock)
      begin
         if (reset == 1'b1)
            begin
               drive_count <= 4'b0000;
            end // if (reset == 1'b1)
         else
            begin
               if ((read_fifo == 1'b1) || (flow == 1'b1))
                  begin
                     drive_count <= 4'b1111;
                  end // if ((read_fifo == 1'b1) || (flow == 1'b1))
               else
                  begin
                     if (drive_count != 4'b0000)
                        begin
                           drive_count <= drive_count -1;
                        end // if (drive_count != 4'b0000)
                  end // else: !if((read_fifo == 1'b1) || (flow == 1'b1))
            end // else: !if(reset == 1'b1)
      end // always@ (posedge clock)
   
   
   
   
   // This process handles the output shift register. Note that the
   // shift register is normally loaded from the FIFO, but may also
   // be loaded with flow control messages.
   always@(posedge clock)
      begin
         if (reset == 1'b1)
            begin
               read_ptr <= 2'b00;
               out_shift[14:0] <= 15'b111111111111111;
            end // if (reset == 1'b1)
         else
            begin
               if (read_fifo == 1'b1)
                  begin
                     out_shift = {2'b10,fifo[read_ptr],1'b0};
                     read_ptr <= read_ptr + 1;
                  end // if (read_fifo == 1'b1)
               else
                  begin
                     if ((flow == 1'b1) && (flow_halt == 1'b1))
                        begin
                           out_shift <= 15'b100000000101000;
                        end // if ((flow == 1'b1) && (flow_halt == 1'b1))
                     else
                        begin
                           if ((flow == 1'b1) && (flow_halt == 1'b0))
                              begin
                                 out_shift <= 15'b100000001001000;
                              end // if ((flow == 1'b1) && (flow_halt == 1'b0))
                           else
                              begin
                                 out_shift[13:0] <= out_shift[14:1];
                                 out_shift[14] <= 1'b1;
                              end // else: !if((flow == 1'b1) && (flow_halt == 1'b0))
                        end // else: !if((flow == 1'b1) && (flow_halt == 1'b1))
                  end // else: !if(read_fifo == 1'b1)
            end // else: !if(reset == 1'b1)
      end // always@ (posedge clock)
   
   
   // This process calculates parity on the output frame.
   always@(posedge clock)
      begin
         if (drive_count == 4'b1110)
            begin
               parity <= out_shift[0];
            end // if (drive_count == 4'b1110)
         else
            begin
               parity <= parity ^ out_shift[0];
            end // else: !if(drive_count == 4'b1110)
      end // always@ (posedge clock)
   
   // This process inserts the newly calculated parity into the
   // output frame.
   always@(out_shift or parity or drive_count)
      begin
         if (drive_count != 4'b0010)
            begin
               out_data <= out_shift[0];
            end // if (drive_count != 4'b0010)
         else
            begin
               out_data <= parity;
            end // else: !if(drive_count != 4'b0010)
      end // always@ (out_shift or parity or drive_count)
   
endmodule // out_channel
