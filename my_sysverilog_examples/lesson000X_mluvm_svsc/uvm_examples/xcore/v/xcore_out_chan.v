/*--------------------------------------------------------------------------- 
File name   : xcore_out_chan.v
Title       : XCore output channel
Project     : XCore eVC
Developers  : Richard Vialls
Created     : 2002-05-21
Description : This block provides an XSerial transmitter
Notes       : The xserial_tx_clock should not be higher nominal frequency
            : than the xserial_tx_clock.
---------------------------------------------------------------------------
Copyright (c) 2002-2010 Cadence Design Systems,Inc.All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME

---------------------------------------------------------------------------*/
`timescale 1ns/1ns

module  xcore_out_chan(xbus_clock,
                       xbus_reset,
                       frame,
                       frame_req,
                       frame_ack,
                       halted,
                       xserial_tx_clock,
                       xserial_tx_data);
   
   input xbus_clock;
   input xbus_reset;
   input [11:0] frame ; // the frame to be transmitted
   input        frame_req; // held high to send frame until frame_ack goes high
   output       frame_ack; // indicates frame sent.
   input        halted; // high if HALT message has been received
   
   
   input        xserial_tx_clock;
   output       xserial_tx_data;
   
   
   wire         xbus_clock;
   wire         xbus_reset;
   wire [11:0]  frame ; // the frame to be transmitted
   wire         frame_req; // held high to send frame until frame_ack goes high
   reg          frame_ack; // indicates frame sent.
   wire         halted; // high if HALT message has been received
   
   
   wire         xserial_tx_clock;
   reg          xserial_tx_data;
   
   reg          frame_req_c;
   reg          frame_req_cc;
   reg          latch_frame;
   reg          frame_done;
   reg          frame_done_c;
   
   reg [14:0]   shift_reg;
   reg [3:0]    drive_count;
   reg          parity;

`ifdef XCORE_SIM
//Transaction creation for tx_frame   
trview_tx_frame: cover property (
     @(posedge xbus_clock) (
                   $rose(frame_ack) ##[1:$] $rose(drive_count == 4'b0000)));

`endif
   
   
   // This process crosses the frame request signal into the XSerial TX cloock
   // domain.
   always@(posedge xserial_tx_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               frame_req_c <= 1'b0;
               frame_req_cc <= 1'b0;
            end // if (xbus_reset == 1'b1)
         else
            begin
               frame_req_cc <= frame_req_c;
               frame_req_c <= frame_req;
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xserial_tx_clock)
   
         
        
   
   // This process determines if a new request to send a frame has been
   // received and the shift register is ready to send the next frame.
   always@(frame_req_cc or frame_done or drive_count or halted)
      begin
         if((frame_req_cc == 1'b1) && (frame_done == 1'b0) && (drive_count == 4'b0000)
            && (halted == 1'b0))
            begin
               latch_frame <= 1'b1;
            end // if ((frame_req_cc == 1'b1) && (frame_done == 1'b0) && (drive_count == 4'b0000)...
         else
            begin
               latch_frame <= 1'b0;
            end // else: !if((frame_req_cc == 1'b1) && (frame_done == 1'b0) && (drive_count == 4'b0000)...
      end // always@ (frame_req_cc or frame_done or drive_count or halted)
   
    
   // This process generates the frame_done signal which indicates that the
   // frame has been latched into the shift register but the core hasn't yet
   // de-asserted frame_req.
   always@(posedge xserial_tx_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               frame_done <= 1'b0;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if (latch_frame == 1'b1)
                  begin
                     frame_done <= 1'b1;
                  end // if (latch_frame == 1'b1)
               else
                  begin
                     if (frame_req_cc == 1'b0)
                        begin
                           frame_done <= 1'b0;
                        end // if (frame_req_cc == 1'b0)
                  end // else: !if(latch_frame == 1'b1)
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xserial_tx_clock)
   
   
   // This process double clocks the frame_done signal into the XBus clock
   // domain to form the frame_ack signal.
   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               frame_done_c <= 1'b0;
               frame_ack <= 1'b0;
            end // if (xbus_reset == 1'b1)
         else
            begin
               frame_ack <= frame_done_c;
               frame_done_c <= frame_done;
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)
   
               
               
   
   // This process counts the bits sent to the output port.
   always@(posedge xserial_tx_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               drive_count <= 4'b0000;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if (latch_frame == 1'b1)
                  begin
                     drive_count <= 4'b1110;
                  end // if (latch_frame == 1'b1)
               else
                  begin
                     if (drive_count != 4'b0000)
                        begin
                           drive_count <= drive_count - 4'b0001;
                        end // if (drive_count != 4'b0000)
                  end // else: !if(latch_frame == 1'b1)
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xserial_tx_clock)
   
   // This process shifts the bits to form the serial frame.
   always@(posedge xserial_tx_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               shift_reg <= 15'b111111111111111;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if (latch_frame == 1'b1)
                  begin
                     shift_reg <= {2'b10,frame,1'b0};
                  end // if (latch_frame == 1'b1)
               else
                  begin
                     shift_reg [13:0] <= shift_reg[14:1];
                     shift_reg[14] <= 1'b1;
                  end // else: !if(latch_frame == 1'b1)
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xserial_tx_clock)
   
                 
         

   // This process calculates the parity as the frame is shifted out.
   always@(posedge xserial_tx_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               parity <= 1'b0;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if (drive_count == 4'b1110)
                  begin
                     parity <= 1'b0;
                  end // if (drive_count == 4'b1110)
               else
                  begin
                     parity <= parity ^ shift_reg[0];
                  end // else: !if(drive_count == 4'b1110)
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xserial_tx_clock)
   
   
   // This process inserts the parity into the outgoing serial data stream.
   always@(posedge xserial_tx_clock)
      begin
         if (drive_count == 4'b0001)
            begin
               xserial_tx_data <= parity;
            end // if (drive_count == 4'b0001)
         else
            begin
               xserial_tx_data <= shift_reg[0];
            end // else: !if(drive_count == 4'b0001)
      end // always@ (posedge xserial_tx_clock)
endmodule // xcore_out_chan

