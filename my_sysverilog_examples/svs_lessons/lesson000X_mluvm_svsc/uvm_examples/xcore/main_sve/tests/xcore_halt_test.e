----------------------------------------------------------------------------
----------------------------------------------------------------------------

File name    : xcore_halt_test.e
Title        : XCore eVC demo - example testcase file
Project      : XCore eVC
Created On   : 2008
Description  : 
Notes        : Behaviour of XCore (TX or not TX) depends on when the HALT 
             : frame arrives. The test does not check XCore's behaivour.
             : Check should be part of the eVC
             : It demonstrates setting effect of a check, using it name -
             : set_check_by_name("has_protocol_checker xserial_monitor_u", 
             :                   "exp_send_while_not_ready", 
             :                   WARNING);
----------------------------------------------------------------------------
>>>>>>>>>>>>>>>>>>>>>>>>>>> COPYRIGHT NOTICE <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
----------------------------------------------------------------------------
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
---------------------------------------------------------------------------

<'

import xcore/main_sve/main_sve_config;
import xcore/main_sve/tests/setup_test; 



extend xserial_sequence_kind : [XCORE_SEND_HALT, 
                                XCORE_SEND_RESUME,
                                XSERIAL_SEND_HALT,
                                XSERIAL_SEND_RESUME];

extend XSERIAL_SEND_HALT xserial_sequence {
    
    keep frame.payload is a MESSAGE xserial_frame_payload_s (MP) and
      (MP.frame_message == HALT);
    keep frame.payload is a MESSAGE xserial_frame_payload_s;
    
    body() @driver.clock is {
        do frame;
    }; 
};


extend XCORE_SEND_HALT xserial_sequence {
    !send_halt_frame : XSERIAL_SEND_HALT xserial_sequence;
    
    body() @driver.clock is only {
        do send_halt_frame;
    }; -- body() @driver....

}; -- extend XCORE...


extend XSERIAL_SEND_RESUME xserial_sequence {
   keep frame.payload is a MESSAGE xserial_frame_payload_s;
    keep frame.payload is a MESSAGE xserial_frame_payload_s (MP) and
      (MP.frame_message == RESUME);

    body() @driver.clock is {
        do frame;
    }; 
};



extend XCORE_SEND_RESUME xserial_sequence {
   !send_resume_frame : XSERIAL_SEND_RESUME xserial_sequence;

   body() @driver.clock is only {
      do send_resume_frame;
   }; -- body() @driver....

}; -- extend XCORE...


extend MAIN MAIN_TEST xcore_combined_sequence {
   !program_xcore_to_tx : XCORE_XBUS_WRITE vr_ad_sequence;
       keep program_xcore_to_tx.driver == driver.xcore_regs_driver;
   
   !send_halt_frame     : XCORE_SEND_HALT xserial_sequence;
       keep send_halt_frame.driver == driver.xserial_driver;

   !send_resume_frame   : XCORE_SEND_RESUME xserial_sequence;
       keep send_resume_frame.driver == driver.xserial_driver;
       
   tx_frames_before : uint;
       keep soft tx_frames_before in [4..10];

   tx_frames_after  : uint;
       keep soft tx_frames_after in [4..10];

   wait_before_resume : uint;
       keep soft wait_before_resume in [400..1000];

   inter_tx_delay   : uint;
       keep soft inter_tx_delay in [10..100];

    keep prevent_test_done;
    
   body() @driver.clock is only {
 
      wait [100] * cycle;
      
       -- Write TX frames, for the XCore to transmit
       for i from 0 to tx_frames_before - 1 {
           do program_xcore_to_tx;
       }; 
       
       -- Send a HALT frame. There should be some TX frames in the fifo
       do send_halt_frame; 

       -- Continue to write TX frames, and release the XCore by 
       -- sending a RESUME frame
       all of {
           {
               for i from 0 to tx_frames_after - 1 {
                   gen inter_tx_delay;
                   wait [inter_tx_delay] * cycle;
                   do program_xcore_to_tx;
               }; -- for i from 0 to...
           };
           {
               wait [wait_before_resume] * cycle;
               do send_resume_frame; 
           }; 

      }; -- all of

      wait [1000] * cycle;
      stop_run();
   }; -- body() @driver.clock

}; -- extend MAIN MAIN_TEST xcore_combined_sequence


'>
   
<'
extend sys {
    // With some seeds, this test uncover a bug in the design
    setup() is also {
        set_check_by_name("has_protocol_checker xserial_monitor_u", 
                          "exp_send_while_not_ready", 
                          WARNING);
    }; 

 }; 

'>
  
