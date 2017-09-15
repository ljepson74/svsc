----------------------------------------------------------------------------
----------------------------------------------------------------------------

File name    : xcore_xbus_seq_test.e
Title        : XCore eVC demo - example testcase file
Project      : XCore eVC
Created On   : 2008
Purpose      : Demonstrate usage of the XBus sequences in the XCore eVC
Description  : Repeat 7..10 times:
             :   XSerial agent sends 1 XSerial frame to the XCore, 
             :   XBus Master reads the frame from the XCore 
             :   XBus Master write to the XCore, programs it to transmit 
             :   a frame
             :   XCore expected to transmit a frame on the XSerial.
             : Access on the XBus is done using the xbus_master_sequences
             : (not using the registers sequnece).
Notes        :  

----------------------------------------------------------------------------
>>>>>>>>>>>>>>>>>>>>>>>>>>> COPYRIGHT NOTICE <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
----------------------------------------------------------------------------
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide

----------------------------------------------------------------------------
   
<'

import xcore/main_sve/main_sve_config;
import setup_test;

extend XCORE_XSERIAL MAIN MAIN_TEST xserial_sequence {

   -- Send random number of frames to the XCore device
   keep count in [7..10];
   keep sequence.kind == XCORE_SEND_FRAME;

   keep prevent_test_done == TRUE;

};

extend MAIN MAIN_TEST xbus_master_sequence  {

    -- Reflect all input frames back to the output.
    keep sequence.kind in [XCORE_READ_WRITE_FRAME];

    -- Should reflect back all received frames. Expected number of 
    -- frames is <= 10
    keep count == 10;
   
   -- Cannot know how many frames are to be read, this sequence should not 
   -- object to test_done
   keep prevent_test_done == FALSE;

};


-- In this test, accesses are done using the xbus sequence, not the 
-- virtual sequecne
extend MAIN xcore_combined_sequence {
   keep count == 0;
}; 

'>

