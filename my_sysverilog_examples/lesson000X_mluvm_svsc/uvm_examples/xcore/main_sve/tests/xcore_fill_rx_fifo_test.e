----------------------------------------------------------------------------
----------------------------------------------------------------------------

File name    : xcore_fill_rx_fifo_test.e
Title        : XCore eVC demo - example testcase file
Project      : XCore eVC
Created On   : 2008
Description  : XSerial agent sends frames.
             : XCore is expected to transmit HALT frame after 2 frames.
             : XBus agent reads the frames after both are sent.
Notes        :  

----------------------------------------------------------------------------
>>>>>>>>>>>>>>>>>>>>>>>>>>> COPYRIGHT NOTICE <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
----------------------------------------------------------------------------
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
----------------------------------------------------------------------------

<'

import  xcore/main_sve/main_sve_config;
import  xcore/main_sve/tests/setup_test;



extend MAIN MAIN_TEST xcore_combined_sequence {
   keep count == 1;
   keep sequence.kind == XCORE_FILL_RX_FIFO_AND_READ_IT;

   keep prevent_test_done == TRUE;

}; 


extend XCORE_XSERIAL MAIN MAIN_TEST xserial_sequence {
   keep count == 0;
};


extend MAIN vr_ad_sequence { 
   keep count == 0;
};


'>

