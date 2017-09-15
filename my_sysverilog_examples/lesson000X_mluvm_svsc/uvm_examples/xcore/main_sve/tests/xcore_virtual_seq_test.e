----------------------------------------------------------------------------
----------------------------------------------------------------------------

File name    : xcore_virtual_seq_test.e
Title        : XCore eVC demo - example testcase file
Project      : XCore eVC
Created On   : 2008
Description  : XSerial agent sends several XSerial frames to the XCore. 
             : Xbus Master reads all the frames.
             : After the last frame, the XBus master writes 
             : the frame to the XCore (whci should transmit it) 
             :
             : Test implemented using virtual sequences activating 
             : vr_ad and xserial sequences.
Notes        :  

----------------------------------------------------------------------------
>>>>>>>>>>>>>>>>>>>>>>>>>>> COPYRIGHT NOTICE <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
----------------------------------------------------------------------------
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
----------------------------------------------------------------------------

<'

import xcore/main_sve/main_sve_config;
//import setup_test;



extend MAIN MAIN_TEST xcore_combined_sequence {
    !xserial_to_xbus          : XCORE_XSERIAL_TO_XBUS 
                                               xcore_combined_sequence;
    !xserial_to_xbus_loopback : XCORE_XSERIAL_TO_XBUS_LOOPBACK 
                                               xcore_combined_sequence;
     

    body() @driver.clock is only {
        do xserial_to_xbus;
        do xserial_to_xbus;
        do xserial_to_xbus;
        
        wait [300] * cycle;

        do xserial_to_xbus_loopback;
    }; 

};


'>

