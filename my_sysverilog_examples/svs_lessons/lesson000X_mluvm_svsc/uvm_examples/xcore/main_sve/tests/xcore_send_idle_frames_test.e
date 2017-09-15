----------------------------------------------------------------------------
----------------------------------------------------------------------------

File name    : xcore_send_idle_frames_test.e
Title        : XCore eVC demo - example testcase file
Project      : XCore eVC
Created On   : 2008
Description  : Send 5 frames on XSserial, not all DATA. XBus reads and
             : writes back all the DATA frames.
Notes        : This test uncover a bug in the XCore. 
             : It demonstrates setting effect of a check, using it name -
             :         set_check_by_name("xserial_scoreboard_u", 
             :             "scbd_empty", 
             :             WARNING);
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

   -- Send exactly 5 frames to the XCore device
   keep count == 5;
   keep sequence.kind == XCORE_SEND_FRAME;

   keep prevent_test_done == TRUE; 
};


extend XCORE_XSERIAL MAIN POST_TEST xserial_sequence {
   keep drain_time == 40;
};

-- About half of the sent frames are to be messages
extend xserial_frame_payload_s {
    keep frame_format.reset_soft();
    keep soft frame_format == select {
        50 : DATA;
        50 : MESSAGE;
    }; 
}; 

-- Only IDLE messages
extend MESSAGE xserial_frame_payload_s {
  keep frame_message == IDLE;
}; 

-- Program the XCore to read the frames
extend MAIN vr_ad_sequence {

    -- Reflect all input frames back to the output.
    keep sequence.kind in [XCORE_XBUS_READ_WRITE];

    -- Reflect maximum 5 frames.
    keep count == 5;

   -- Not all frames are expected to be reflected (not all are DATA),
   -- so this sequence should not stop the test
   keep prevent_test_done == FALSE; 
   
};

-- No virtaul sequence in this test, scneraio created by BFM sequences
extend MAIN MAIN_TEST xcore_combined_sequence {
    keep count == 0;
};



'>

   
   
