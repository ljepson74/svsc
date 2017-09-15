----------------------------------------------------------------------------
----------------------------------------------------------------------------

File name    : xcore_error_rx_frames_test.e
Title        : XCore eVC demo - example testcase file
Project      : XCore eVC
Created On   : 2008
Description  : Send some frames to the XCore on the XSerial.
             : ~30% of them have bad parity
Notes        :  

----------------------------------------------------------------------------
>>>>>>>>>>>>>>>>>>>>>>>>>>> COPYRIGHT NOTICE <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
----------------------------------------------------------------------------
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
---------------------------------------------------------------------------

<'

import xcore/main_sve/main_sve_config;
import setup_test;



extend MAIN MAIN_TEST xserial_sequence {
    keep count in [4..10];
    keep sequence.kind == XCORE_SEND_FRAME;

    -- Test must not stop before the serial sequence finishes
    keep prevent_test_done == TRUE;
}; 

-- Read all the sent frames
extend MAIN vr_ad_sequence {
    keep sequence.kind == XCORE_XBUS_READ_WRITE;

     keep count == 10;
    
    -- The sequence polls the registers to read 10 frames.
    -- Since there can be less than 10 frames in the test (depends on the 
    -- xserial_sequence), this sequence must not object to end of test.
    -- It keeps reading the registers until either read 10 frames, or the 
    -- test ended. Which ever comes first.
    keep prevent_test_done == FALSE;
};

-- Each frame has a 30% probability to have parity error
extend  xserial_frame_s {  
    keep bad_parity.reset_soft();
    
    keep soft bad_parity == select {
        30 : TRUE;
        70 : FALSE;
    };
    
};

extend xserial_frame_payload_s {
   keep frame_format == DATA;
};

-- No virtaul sequence in this test, scneraio created by BFM sequences
extend MAIN MAIN_TEST xcore_combined_sequence {
    keep count == 0;
};
'>
   
<'
extend sys {
    bad_counter : uint;
    good_counter : uint;
    keep bad_counter == 0;
    keep good_counter == 0;
    
    check() is also {
        message(LOW, "frames with bad parity: ", bad_counter, 
                "\nframes with good parity: ",   good_counter  );
    };
};

extend  xserial_frame_s {
    on tx_frame_done {
        if  bad_parity then {
            sys.bad_counter += 1;
        } else {
            sys.good_counter += 1;
        };
        message(LOW, "bad_parity is: " , bad_parity);
    };
};
'>







