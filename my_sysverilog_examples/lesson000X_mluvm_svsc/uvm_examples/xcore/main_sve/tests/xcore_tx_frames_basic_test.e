----------------------------------------------------------------------------
----------------------------------------------------------------------------

File name    : xcore_tx_frames_basic_test.e
Title        : XCore eVC demo - example testcase file
Project      : XCore eVC
Created On   : 2008
Description  : XBus writes several frames to the XCore, to be transmited 
             : on the XSerial 
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



extend MAIN vr_ad_sequence {
   keep count in [2..10];
   keep sequence.kind == XCORE_XBUS_WRITE;

     keep prevent_test_done == TRUE;
}; 


-- No virtaul sequence in this test, scneraio created by BFM sequences
extend MAIN xcore_combined_sequence {
    keep count == 0;
};

'>
   
