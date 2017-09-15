/*------------------------------------------------------------------------- 
File name   : xcore_combined_seq_lib.e
Title       : Sequence lib
Project     : XCore eVC
Created     : 2008
Description : Sequences accessing XCore via XBus and XSerial
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide.

-------------------------------------------------------------------------*/ 

<'
package cdn_xcore;
import xcore/e/xcore_combined_sequence_h;
'>

<'
extend xcore_combined_sequence_kind : [XCORE_XSERIAL_TO_XBUS,
                                          XCORE_XSERIAL_TO_XBUS_LOOPBACK,
                                          XCORE_FILL_RX_FIFO,
                                          XCORE_FILL_RX_FIFO_AND_READ_IT];


-- Send one frame via XSerial, XBus read this frame
extend XCORE_XSERIAL_TO_XBUS xcore_combined_sequence {

   body() @driver.clock is {
      
      -- Send one frame to the serial
      do XCORE_SEND_FRAME xserial_sequence;

      -- Bus read the frame 
      do XCORE_XBUS_READ regs_sequence;
   }; -- body() @driver....

};


-- Send one frame via XSerial, XBus read this frame and write it back
extend XCORE_XSERIAL_TO_XBUS_LOOPBACK xcore_combined_sequence {

   body() @driver.clock is {
      
      -- Send one frame to the serial
      do XCORE_SEND_FRAME xserial_sequence;

      -- Bus reads the frame and writes it back 
      do XCORE_XBUS_READ_WRITE regs_sequence;
   }; -- body() @driver....
};


-- Send 2 frames to the XCore. If no reads are issued, 
-- the two frames will fill the RX fifo
extend XCORE_FILL_RX_FIFO xcore_combined_sequence {
   
   keep xserial_sequence.kind == XCORE_SEND_FRAME;

   body() @driver.clock is {  
      -- Send 2 frames to the XCore device to fill its fifo
      for i from 0 to 1 {
         do xserial_sequence;
      }; -- for i from 0 to...
   };
}; -- extend XCORE_FILL_RX_FIFO


-- Send 2 frames to the XCore. If no reads are issued, 
-- the two frames will fill the RX fifo.
-- Then, read the frames
extend XCORE_FILL_RX_FIFO_AND_READ_IT xcore_combined_sequence {
   
   keep xserial_sequence.kind == XCORE_SEND_FRAME;
   keep regs_sequence.kind == XCORE_XBUS_READ;

   body() @driver.clock is {  
      -- Send 2 frames to the XCore device to fill its fifo
      for i from 0 to 1 {
         do xserial_sequence;
      }; -- for i from 0 to...

      
      -- Read the frames from the XCore
      for i from 0 to 1 {
         do regs_sequence;
      }; -- for i from 0 to...

   }; -- body() @driver....

}; -- extend XCORE_FILL_RX_FIFO_AND_READ_IT
'>
  
