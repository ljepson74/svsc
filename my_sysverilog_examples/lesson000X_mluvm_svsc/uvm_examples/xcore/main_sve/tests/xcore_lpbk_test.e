----------------------------------------------------------------------------
----------------------------------------------------------------------------

File name    : xcore_lpbk_test.e
Title        : XCore eVC demo - example testcase file
Project      : XCore eVC
Created On   : 2008
Description  : Repeat 5 times:
             :   XSerial agent sends 1 XSerial frame to the XCore, 
             :   XBus Master reads the frame from the XCore 
             :   XBus Master write to the XCore, programs it to transmit
             :   a frame
             :   XCore expected to transmit a frame on the XSerial.
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

-- Control the XSerial interface - send frames
extend XCORE_XSERIAL MAIN MAIN_TEST xserial_sequence {

   -- Send exactly 5 frames to the XCore device
   keep count == 5;
   keep sequence.kind == XCORE_SEND_FRAME;

     
};



-- Control the XCore - program to read and write frames
extend MAIN vr_ad_sequence {

   -- Reflect all 5 input frames back to the output
   keep count == 5;
   keep sequence.kind == XCORE_XBUS_READ_WRITE;

    
   keep prevent_test_done == TRUE;

};

-- No virtaul sequence in this test, scneraio created by BFM sequences
extend MAIN MAIN_TEST xcore_combined_sequence {
    keep count == 0;
};
'>

