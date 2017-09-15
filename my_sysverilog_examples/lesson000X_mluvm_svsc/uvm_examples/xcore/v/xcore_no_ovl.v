//--------------------------------------------------------------------------- 
//File name   : xcore.v
//Title       : Verilog block providing an XBus to XSerial gateway
//Project     : XCore eVC
//Developers  : Richard Vialls
//Created     : 21-May-2002
//Description : This block sits on the XBus and provides a means of reading
//            : and writing to/from a single XSerial port. Four registers
//            : are provided in the XBus address map. After an XBus reset,
//            : all registers are set to 0. These byte-wide registers occupy
//            : consecutive byte addresses starting at the address specified
//            : by the BASE_ADDR input (which specifies the upper 8 bits of
//            : the BASE_ADDR - the lower 8 bits are always 0). A full 256
//            : bytes of address space are decoded by the block. Attempts to
//            : read/write addresses within this space other than those of the
//            : three registers is treated as an error as is any attempt to do
//            : transfers to this address space larger than a single byte. All
//            : reads and writes are zero wait state.
//            :
//            : The four registers are:
//            : 
//            : XSerial TX data register (offset 0)
//            :    Writing a byte to this register causes that byte to be
//            :    transmitted on the XSerial port. It is illegal to write
//            :    to this register without first reading from it and getting
//            :    bit 0 = 0. Attempting to do this results in a bus error.
//            :    Reading this register returns a flag in bit 0 (all other 
//            :    bits return 0). If the flag is 1, then the port is busy and 
//            :    a further byte cannot yet be sent. If the flag is 0, then 
//            :    the port is not busy and it is safe to write to this 
//            :    register.
//            : 
//            : XSerial TX mode register (offset 1)
//            :    Bits 0-1 of this register form the Destination address of 
//            :    subsequently transmitted frames.
//            :    Bits 2-3 of this register form the frame_kind of 
//            :    subsequently transmitted frames.
//            :    Bits 4-7 are unused and return 0 on reads. They should 
//            :    always be written as 0 for future compatibility
//            :    This register can be written to and read from.
//            :
//            : XSerial RX data register (offset 2)
//            :    If bit 5 of register 3 is 1, then reading this register 
//            :    returns the least significant 8 bits of the frame payload. 
//            :    It is illegal to read this register without first reading 
//            :    the RX mode register and getting bit 5 = 1. Attempting to 
//            :    do this results in a bus error.
//            :    Reading this register causes the information in both this
//            :    register and in register 3 to be discarded and also causes 
//            :    bit 5 of register 3 to be cleared to 0. When the next frame
//            :    is received, both registers will be updated with the new 
//            :    frame information and bit 5 of register 3 will be set to 1 
//            :    again.
//            :    Writing to this register causes a bus error.
//            :
//            : XSerial RX mode register (offset 3)
//            :    Bits 0-1 of this register form the Destination address of 
//            :    the most recently received frame.
//            :    Bits 2-3 of this register form the Frame_kind of the most
//            :    recently received frame.
//            :    Bit 4 of this register is 1 if the most recently received 
//            :    frame has a parity error or 0 if it does not.
//            :    Bit 5 of this register is 1 if registers 2 and 3 contain a 
//            :    valid frame.
//            :    Bits 6-7 are unused and return 0 on reads.
//            :    Writing to this register causes a bus error.
//Notes       : xserial_rx_clock and xserial_tx_clock should run at the same
//            : nominal frequency. This nominal frequency should be not
//            : greater than the nominal frequency of the xbus_clock signal.
//--------------------------------------------------------------------------- 
//Copyright (c) 2005-2010 Cadence Design Systems,Inc.
// All rights reserved worldwide
//(Acquired from Verisity Design,Inc.,2005).
//Please refer to the terms and conditions in $IPCM_HOME


`define ASSERT_ON
`timescale 1ns/1ns

module xcore(base_addr,
             xbus_clock,
             xbus_reset,
             xbus_start,
	     xbus_request,	
	     xbus_grant,
             xbus_addr,
             xbus_size,
             xbus_read,
             xbus_write,
             xbus_bip,
             xbus_data,
             xbus_wait,
             xbus_error,
             xserial_rx_clock,
             xserial_rx_data,
             xserial_tx_clock,
             xserial_tx_data);
   
   input [15:8]base_addr;
   input       xbus_clock;
   input       xbus_reset;
   input       xbus_start;
   input       xbus_request;
   input       xbus_grant;
   input [15:0] xbus_addr;
   input [1:0]  xbus_size;
   input        xbus_read;
   input        xbus_write;
   input        xbus_bip;
   inout [7:0]  xbus_data;
   output       xbus_wait;
   output       xbus_error;
   input        xserial_rx_clock;
   input        xserial_rx_data;
   input        xserial_tx_clock;
   output       xserial_tx_data;
   
   wire [7:0]   xbus_data;
   
   
   
   wire [15:8]  base_addr;
   wire       xbus_clock;
   wire       xbus_reset;
   wire       xbus_start;
   wire       xbus_request;
   wire       xbus_grant;
   wire [15:0] xbus_addr;
   wire [1:0]  xbus_size;
   wire         xbus_read;
   wire         xbus_write;
   wire         xbus_bip;
   reg [7:0]    xcore_xbus_data;
   reg          xbus_wait;
   reg          xbus_error;
   wire         xserial_rx_clock;
   wire         xserial_rx_data;
   wire         xserial_tx_clock;
   wire         xserial_tx_data;
   assign xbus_data = xcore_xbus_data;
   
   
   
   
   
   // RX interface signals
   wire [12:0]  rx_frame; // Next item in RX FIFO
   wire         rx_frame_valid; // high if RX FIFO contains frames
   reg          rx_frame_valid_c; // delayed version of rx_frame_valid_c
   reg          rx_read_fifo;
   wire         halted; // high if HALT message has been received
   wire         flow_req; // high if need to send message to remote end of link
   wire         flow_halt; // high if required message is HALT, low for RESUME
   wire         flow_ack; // high to acknowledge that message has been sent
   
   // TX interface signals
   reg [11:0]   tx_frame; // the frame to be transmitted
   wire         tx_frame_req;
   wire         tx_frame_ack; // indicates frame sent.
   
   // XBus decode signals
   reg          xbus_start_c;
   reg          xbus_selected;
   wire         xbus_reg;
  
   reg          xbus_reg0;
   reg          xbus_reg1;
   reg          xbus_reg2;
   reg          xbus_reg3;
   
   reg          xbus_reg_c;
   reg          xbus_reg0_c ;
   reg          xbus_reg1_c;
   reg          xbus_reg2_c;
   reg          xbus_reg3_c;
   reg          xbus_write_c;

   // internal core signals
   reg [3:0]    tx_mode_reg;
   reg [7:0]    tx_data_reg;
   wire         tx_busy;
   reg          tx_pend;
   wire         tx_busy_reg;
   reg          tx_busy_reg_c; // delayed version of tx_busy_reg
   reg          write_tx_data;
   reg          xbus_error_internal;
   reg          flow;
   reg          tx_halt_req;
   reg          tx_resume_req;
   reg          tx_data_req;
   reg          tx_write_safe; // high if a write to tx_data_reg is safe
   reg          rx_read_safe;  // high if a read from rx_data_reg is safe
   
   
   
   xcore_in_chan in_chan_inst(.xbus_clock(xbus_clock),
                           .xbus_reset(xbus_reset),
                           .frame(rx_frame),
                           .frame_valid(rx_frame_valid),
                           .read_fifo(rx_read_fifo),
                           .halted(halted),
                           .flow_req(flow_req),
                           .flow_halt(flow_halt),
                           .flow_ack(flow_ack),
                           .xserial_rx_clock(xserial_rx_clock),
                           .xserial_rx_data(xserial_rx_data));
   
   xcore_out_chan out_chan_inst(.xbus_clock(xbus_clock),
                             .xbus_reset(xbus_reset),
                             .frame(tx_frame),
                             .frame_req(tx_frame_req),
                             .frame_ack(tx_frame_ack),
                             .halted(halted),
                             .xserial_tx_clock(xserial_tx_clock),
                             .xserial_tx_data(xserial_tx_data));
   
   // If we have requested a frame be sent and the handshaking across the
   // clock domains has not yet finished, then the TX port is busy.
   assign tx_busy = tx_frame_req | tx_frame_ack;
   

   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               xbus_start_c <= 1'b0;
            end // if (xbus_reset == 1'b1)
         else
            begin
               xbus_start_c <= xbus_start;
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)
   
         
    
   // This process determines whether the current XBus address selects this
   // instance of the XCore.
   
   always@(xbus_addr or base_addr)
      begin
         if(xbus_addr[15:8] == base_addr[15:8])
            begin
               xbus_selected <= 1'b1;
            end // if (xbus_addr[15:8] == base_addr[15:8])
         else
            begin
               xbus_selected <= 1'b0;
            end // else: !if(xbus_addr[15:8] == base_addr[15:8])
      end // always@ (xbus_addr or base_addr)
   
   
   
   // This process ensures that the xbus_wait signal is driven low (i.e. no
   // wait states are inserted) at the correct point of the transfer.
   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               xbus_wait <= 1'bz;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if((xbus_start_c == 1'b1) && (xbus_selected == 1'b1) && 
                  ((xbus_read == 1'b1)||(xbus_write == 1'b1)))
                  begin
                     xbus_wait <= 1'b0;
                  end // if ((xbus_start_c == 1'b1) && (xbus_selected == 1'b1) &&...
               else
                  begin
                     xbus_wait <= 1'bz;
                  end // else: !if((xbus_start_c == 1'b1) && (xbus_selected == 1'b1) &&...
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)
   
   
   // xbus_reg is high in the address phase of any transfer directed at this
   // XCore instance.
   //always@(xbus_start_c or xbus_selected or xbus_read or xbus_write)
   //   begin
        // if((xbus_start_c == 1'b1) && (xbus_selected == 1'b1) && ((xbus_read === 1'b1) || (xbus_write === 1'b1)))
        //    begin
        //       xbus_reg <= 1'b1;
        //    end // if ((xbus_start_c == 1'b1) && (xbus_selected == 1'b1) && ((xbus_read === 1'b1) || (xbus_write === 1'b1)))
        // else
        //    begin
        //       xbus_reg <=1'b0;
        //    end // else: !if((xbus_start_c == 1'b1) && (xbus_selected == 1'b1) && ((xbus_read === 1'b1) || (xbus_write === 1'b1)))
      //end // always@ (xbus_start_c or xbus_selected or xbus_read or xbus_write)
   
   assign xbus_reg = xbus_start_c & xbus_selected & (xbus_read | xbus_write);
   
    
   // This process further decodes the address signals to determine if any of
   // the four internal registers are selected.
   
   
   always@(xbus_addr)
      begin
         if (xbus_addr[7:0] == 8'b00000000)
            begin
               xbus_reg0 <= 1'b1;
            end // if (xbus_addr[7:0] == 8'b00000000)
         else
            begin
               xbus_reg0 <= 1'b0;
            end // else: !if(xbus_addr[7:0] == 8'b00000000)
         if(xbus_addr[7:0] == 8'b00000001)
            begin
               xbus_reg1 <= 1'b1;
            end // if (xbus_addr[7:0] == 8'b00000001)
         else
            begin
               xbus_reg1 <= 1'b0;
            end // else: !if(xbus_addr[7:0] == 8'b00000001)
         if(xbus_addr[7:0] == 8'b00000010)
            begin
               xbus_reg2 <= 1'b1;
            end // if (xbus_addr[7:0] == 8'b00000010)
         else
            begin
               xbus_reg2 <= 1'b0;
            end // else: !if(xbus_addr[7:0] == 8'b00000010)
         if (xbus_addr[7:0] == 8'b00000011)
            begin
               xbus_reg3 <= 1'b1;
            end // if (xbus_addr[7:0] == 8'b00000011)
         else
            begin
               xbus_reg3 <= 1'b0;
            end // else: !if(xbus_addr[7:0] == 8'b00000011)
      end // always@ (xbus_addr)
   
   
    
   // This process provides delayed versions of the various register signals
   // and the write signal that are valid in the data phase.
  
   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               xbus_reg_c <= 1'b0;
               xbus_reg0_c <= 1'b0;
               xbus_reg1_c <= 1'b0;
               xbus_reg2_c <= 1'b0;
               xbus_reg3_c <= 1'b0;
               xbus_write_c <= 1'b0;
            end // if (xbus_reset == 1'b1)
         else
            begin
               xbus_reg_c <= xbus_reg;
               xbus_reg0_c <= xbus_reg & xbus_reg0;
               xbus_reg1_c <= xbus_reg & xbus_reg1;
               xbus_reg2_c <= xbus_reg & xbus_reg2;
               xbus_reg3_c <= xbus_reg & xbus_reg3;
               xbus_write_c <= xbus_write;
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)
   
    
   // This process determines if the transfer should return a bus error.
   // Possible errors are: size of transfer is larger than 1 byte; block
   // is selected but address does not select one of the four registers;
   // an attempt to write to register 0 when it is busy; a write to
   // register 2 or 3; Attempt to read register 2 when there is no valid
   // frame to be read.
   
   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               xbus_error_internal <= 1'b0;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if (xbus_reg == 1'b1)
                  begin
                     if(xbus_size != 2'b00)
                        begin
                           xbus_error_internal <= 1'b1;
                        end // if (xbus_size != 2'b00)
                     else
                        begin
                           if((xbus_reg0 == 1'b0) && (xbus_reg1 == 1'b0)
                              && (xbus_reg2 == 1'b0) && (xbus_reg3 == 1'b0))
                              begin
                                 xbus_error_internal <= 1'b1;
                              end // if ((xbus_reg0 == 1'b0) && (xbus_reg1 == 1'b0)...
                           else
                              begin
                                 if((xbus_reg0 == 1'b1) && (xbus_write == 1'b1)
                                    && (tx_write_safe == 1'b0))
                                    begin
                                       xbus_error_internal <= 1'b1;
                                    end // if ((xbus_reg0 == 1'b1) && (xbus_write == 1'b1)...
                                 else
                                    begin
                                       if (((xbus_reg2 == 1'b1) || (xbus_reg3 == 1'b1)) 
                                           && (xbus_write == 1'b1))
                                          begin
                                             xbus_error_internal <= 1'b1;
                                          end // if (((xbus_reg2 == 1'b1) || (xbus_reg3 == 1'b1))...
                                       else
                                          begin
                                             if((xbus_reg2 == 1'b1) && (xbus_read == 1'b1)
                                                && (rx_read_safe == 1'b0))
                                                begin
                                                   xbus_error_internal <= 1'b1;
                                                end // if ((xbus_reg2 == 1'b1) && (xbus_read == 1'b1)...
                                             else
                                                begin
                                                   xbus_error_internal <= 1'b0;
                                                end // else: !if((xbus_reg2 == 1'b1) && (xbus_read == 1'b1)...
                                          end // else: !if(((xbus_reg2 == 1'b1) || (xbus_reg3 == 1'b1))...
                                    end // else: !if((xbus_reg0 == 1'b1) && (xbus_write == 1'b1)...
                              end // else: !if((xbus_reg0 == 1'b0) && (xbus_reg1 == 1'b0)...
                        end // else: !if(xbus_size != 2'b00)
                  end // if (xbus_reg == 1'b1)
               else
                  begin
                     xbus_error_internal <= 1'b0;
                  end // else: !if(xbus_reg == 1'b1)
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)
   
                     
   
   
   
   
   
   
   
   
   
   // This process drives the xbus_error signal at the appropriate point
   // in the transfer.
   always@(xbus_reset or xbus_reg_c or xbus_error_internal)
      begin
         if(xbus_reset == 1'b1)
            begin
               xbus_error <= 1'bz;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if (xbus_reg_c == 1'b1)
                  begin
                     xbus_error <= xbus_error_internal;
                  end // if (xbus_reg_c == 1'b1)
               else
                  begin
                     xbus_error <= 1'bz;
                  end // else: !if(xbus_reg_c == 1'b1)
            end // else: !if(xbus_reset == 1'b1)
      end // always (xbus_reset or xbus_reg_c or xbus_error_internal)
   
   
   
    
   // This process drives the data bus on reads.
   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               xcore_xbus_data <= 8'bZZZZZZZZ;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if((xbus_start_c == 1'b1) && (xbus_selected == 1'b1) && (xbus_reg0 == 1'b1)
                  && (xbus_read == 1'b1))
                  begin
                     xcore_xbus_data <= {7'b0000000 , tx_busy_reg};
                  end // if ((xbus_start_c == 1'b1) && (xbus_selected == 1'b1) && (xbus_reg0 == 1'b1)...
               else
                  begin
                     if ((xbus_start_c == 1'b1) && (xbus_selected == 1'b1) && (xbus_reg1 == 1'b1)
                         && (xbus_read == 1'b1))
                        begin
                           xcore_xbus_data <= {4'b0000,tx_frame[11:8]};
                        end // if ((xbus_start_c == 1'b1) && (xbus_selected == 1'b1) && (xbus_reg1 == 1'b1)...
                     else
                        begin
                           if ((xbus_start_c == 1'b1) && (xbus_selected == 1'b1) && (xbus_reg2 == 1'b1)
                               && (xbus_read == 1'b1))
                              begin
                                 xcore_xbus_data <= rx_frame[11:4];
                              end // if ((xbus_start_c == 1'b1) && (xbus_selected == 1'b1) && (xbus_reg2 == 1'b1)...
                           else
                              begin
                                 if((xbus_start_c == 1'b1) && (xbus_selected == 1'b1) && (xbus_reg3 == 1'b1) 
                                    && (xbus_read == 1'b1))
                                    begin
                                       if(rx_frame_valid == 1'b1)
                                          begin
                                             xcore_xbus_data <= {3'b001, rx_frame[12], rx_frame[3:0]};
                                          end // if (rx_frame_valid == 1'b1)
                                       else
                                          begin
                                             xcore_xbus_data <= 8'b00000000;
                                          end // else: !if(rx_frame_valid == 1'b1)
                                    end // if ((xbus_start_c == 1'b1) && (xbus_selected == 1'b1) && (xbus_reg3 == 1'b1)...
                                 else
                                    begin
                                       xcore_xbus_data <= 8'bZZZZZZZZ;
                                    end // else: !if((xbus_start_c == 1'b1) && (xbus_selected == 1'b1) && (xbus_reg3 == 1'b1)...
                              end // else: !if((xbus_start_c == 1'b1) && (xbus_selected == 1'b1) && (xbus_reg2 == 1'b1)...
                        end // else: !if((xbus_start_c == 1'b1) && (xbus_selected == 1'b1) && (xbus_reg1 == 1'b1)...
                  end // else: !if((xbus_start_c == 1'b1) && (xbus_selected == 1'b1) && (xbus_reg0 == 1'b1)...
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)


   // This process determines when it is safe to read from the RX_DATA register and when this
   // would generate a bus error.
   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               rx_read_safe <= 1'b0;
               rx_frame_valid_c <= 1'b0;
            end // if (xbus_reset == 1'b1)
         else
            begin
               rx_frame_valid_c <= rx_frame_valid;
               if ((xbus_reg2_c == 1'b1) && (xbus_write_c == 1'b0) &&
                   (xbus_error_internal == 1'b0))
                  begin
                     rx_read_safe <= 1'b0;
                  end // if ((xbus_reg2_c == 1'b1) && (xbus_write_c == 1'b0) &&...
               else
                  begin
                     if ((xbus_reg3_c == 1'b1) && (xbus_write_c == 1'b0) && 
                         (xbus_error_internal == 1'b0) && (rx_frame_valid_c == 1'b1))
                        begin
                           rx_read_safe <= 1'b1;
                        end
                  end // else: !if((xbus_reg2_c == 1'b1) && (xbus_write_c == 1'b0) &&...
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)
   
   
   // This process determines when a frame is read from the input channel FIFO
   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               rx_read_fifo <= 1'b0;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if ((xbus_reg2_c == 1'b1) && (xbus_write_c == 1'b0) &&
                   (xbus_error_internal == 1'b0))
                  begin
                     rx_read_fifo <= 1'b1;
                  end // if ((xbus_reg2_c == 1'b1) && (xbus_write_c == 1'b0) &&...
               else
                  begin
                     rx_read_fifo <= 1'b0;
                  end // else: !if((xbus_reg2_c == 1'b1) && (xbus_write_c == 1'b0) &&...
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)
   
   
   // This process implements writes to register 1.
   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               tx_mode_reg <= 4'b0000;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if((xbus_reg1_c == 1'b1) && (xbus_write_c == 1'b1)
                  && (xbus_error_internal == 1'b0))
                  begin
                     tx_mode_reg <= xbus_data[3:0];
                  end // if ((xbus_reg1_c == 1'b1) && (xbus_write_c == 1'b1)...
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)
   
   
   // This process determines when a write to register 0 has happened.
   always@(xbus_reg0_c or xbus_write_c or xbus_error_internal)
      begin
         if((xbus_reg0_c == 1'b1) && (xbus_write_c == 1'b1)
            && (xbus_error_internal == 1'b0))
            begin
               write_tx_data <= 1'b1;
            end // if ((xbus_reg0_c == 1'b1) && (xbus_write_c == 1'b1)...
         else
            begin
               write_tx_data <= 1'b0;
            end // else: !if((xbus_reg0_c == 1'b1) && (xbus_write_c == 1'b1)...
      end // always@ (xbus_reg0_c or xbus_write_c or xbus_error_internal)
   
   
   // This process determines when it is safe to write to the TX_DATA register and when this
   // would generate a bus error.
   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               tx_write_safe <= 1'b0;
               tx_busy_reg_c <= 1'b0;
            end // if (xbus_reset == 1'b1)
         else
            begin
               tx_busy_reg_c <= tx_busy_reg;
               if (write_tx_data == 1'b1)
                  begin
                     tx_write_safe <= 1'b0;
                  end // if (write_tx_data == 1'b1)
               else
                  begin
                     if ((xbus_reg0_c == 1'b1) && (xbus_write_c == 1'b0) && 
                         (xbus_error_internal == 1'b0) && (tx_busy_reg_c == 1'b0))
                        begin
                           tx_write_safe <= 1'b1;
                        end
                  end // else: !if((xbus_reg0_c == 1'b1) && (xbus_write_c == 1'b0) &&...
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)


   // This process implements writes to register 0.
   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               tx_data_reg[7:0] <= 8'b00000000;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if (write_tx_data == 1'b1)
                  begin
                     tx_data_reg[7:0] <= xbus_data;
                  end // if (write_tx_data == 1'b1)
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)
   
         
               
   
   // This process determines when we need to send a flow control message.
   // These take priority over all other frames.
   always@(flow_req or tx_busy)
      begin
         if((flow_req == 1'b1) && (tx_busy == 1'b0))
            begin
               flow <= 1'b1;
            end // if ((flow_req == 1'b1) && (tx_busy == 1'b0))
         else
            begin
               flow <= 1'b0;
            end // else: !if((flow_req == 1'b1) && (tx_busy == 1'b0))
      end // always@ (flow_req or tx_busy)
   
   
   // Make sure we acknowledge that the flow control message has been sent.
   assign flow_ack = flow;
   
   
   // This process keeps track of any data sends that have been pre-empted
   // by a flow control request. These get send after the flow control message
   // has been sent.
   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               tx_pend <= 1'b0;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if ((write_tx_data == 1'b1) && ((tx_busy == 1'b1) || (flow == 1'b1)))
                  begin
                     tx_pend <= 1'b1;
                  end // ((write_tx_data == 1'b1) && ((tx_busy == 1'b1) || (flow == 1'b1))
               else
                  begin
                     if ((tx_pend == 1'b1) && (tx_busy == 1'b0) && (flow == 1'b0))
                        begin
                           // Following line change May 2007 - It used to be 
                           // set to 1, I modified to 0. efrat
                           tx_pend <= 1'b0;
                        end
                  end // else: !((write_tx_data == 1'b1) && ((tx_busy == 1'b1) || (flow == 1'b1))
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)
   
                           
   
   // This process creates HALT and RESUME requests to the output channel as
   // required.
   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               tx_halt_req <= 1'b0;
               tx_resume_req <= 1'b0;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if((flow == 1'b1) && (flow_halt == 1'b1))
                  begin
                     tx_halt_req <= 1'b1;
                  end // if ((flow == 1'b1) && (flow_halt == 1'b1))
               else
                  begin
                     if ((flow == 1'b1) && (flow_halt == 1'b0))
                        begin
                           tx_resume_req <= 1'b1;
                        end // if ((flow == 1'b1) && (flow_halt == 1'b0))
                     else
                        begin
                           if(tx_frame_ack == 1'b1)
                              begin
                                 tx_halt_req <= 1'b0;
                                 tx_resume_req <= 1'b0;
                              end // if (tx_frame_ack == 1'b1)
                        end // else: !if((flow == 1'b1) && (flow_halt == 1'b0))
                  end // else: !if((flow == 1'b1) && (flow_halt == 1'b1))
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)
   
                           
   
   // This process ensures that writes to register 0 cause the output channel
   // to be kicked into play.
   always@(posedge xbus_clock)
      begin
         if (xbus_reset == 1'b1)
            begin
               tx_data_req <= 1'b0;
            end // if (xbus_reset == 1'b1)
         else
            begin
               if ((write_tx_data == 1'b1) && (tx_busy == 1'b0) && (flow == 1'b0))
                  begin
                     tx_data_req <= 1'b1;
                  end // if ((write_tx_data == 1'b1) && (tx_busy == 1'b0) && (flow == 1'b0))
               else
                  begin
                     if ((tx_pend == 1'b1) && (tx_busy == 1'b0) && (flow == 1'b0))
                        begin
                           tx_data_req <= 1'b1;
                        end // if ((tx_pend == 1'b1) && (tx_busy == 1'b0) && (flow == 1'b0))
                     else
                        begin
                           if (tx_frame_ack == 1'b1)
                              begin
                                 tx_data_req <= 1'b0;
                              end // if (tx_frame_ack == 1'b1)
                        end // else: !if ((tx_pend == 1'b1) && (tx_busy == 1'b0) && (flow == 1'b0))
                  end // else: !if ((write_tx_data == 1'b1) && (tx_busy == 1'b0) && (flow == 1'b0))
            end // else: !if(xbus_reset == 1'b1)
      end // always@ (posedge xbus_clock)
   
   
   // XBus should see 'busy' if either the TX channel is busy or we have a data
   // frame pending.
   assign tx_busy_reg = tx_busy | tx_pend;
   
  
   // If either a flow message or a data frame needs to be sent, inform the TX
   // channel.
   assign tx_frame_req = tx_halt_req | tx_resume_req | tx_data_req;
   
         
   // This process decides whether user data or flow control messages get sent
   // to the output channel.
   always@(tx_halt_req or tx_resume_req or tx_data_reg or tx_mode_reg)
      begin
         if(tx_halt_req == 1'b1)
            begin
               tx_frame <= 12'b000000010100;
            end // if (tx_halt_req == 1'b1)
         else
            begin
               if (tx_resume_req == 1'b1)
                  begin
                     tx_frame <= 12'b000000100100;
                  end // if (tx_resume_reg == 1'b1)
               else
                  begin
                  if ((tx_mode_reg[3:2] == 2'b01) && (tx_data_reg == 8'b00000001))
                     begin
                     tx_frame <= 12'b000000000100;
                     end
                  else
                     begin
                     if ((tx_mode_reg[3:2] == 2'b01) && (tx_data_reg == 8'b00000010))
                        begin
                        tx_frame <= 12'b000000000100;
                        end
                     else
                        begin
                        tx_frame <= {tx_data_reg , tx_mode_reg};
                        end
                     end
                  end // else: !if(tx_resume_reg == 1'b1)
            end // else: !if(tx_halt_req == 1'b1)
      end // always@ (tx_halt_req or tx_resume_req or tx_data_reg or tx_mode_reg)
endmodule // xcore

