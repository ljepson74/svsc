----------------------------------------------------------------------------
----------------------------------------------------------------------------

File name    : xcore_rerun_test.e
Title        : Reset test
Project      : XCore eVC
Created On   : 2008
Description  : Reset scneario:
             :
             : During INIT_LINK phase reset XBus (using rerun_phase)).
             : To make it interesting, making sure all this takes some time,
             : add fake activities
             : XSerial components should wait until xbus is out of reset.
             :
             : Repeat 3 times:
             :   XSerial agent sends 1 XSerial frame to the XCore, 
             :   XBus Master reads the frame from the XCore 
             :   XBus Master write to the XCore, programs it to transmit
             :   a frame
             :   XCore expected to transmit a frame on the XSerial.
             : In total:
             :  XCore expected to transmit 3 frames on the XSerial.
             :
             : Verbosity of logger is set to FULL, to see all TESTFLOW
             : related messages coming from the eVCs.
             :
             : For seeing messages of the utility itself, set the verbosity 
             : of the tag TESTFLOW to FULL.
             :
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

   -- Send exactly 3 frames to the XCore device
   keep count == 3;
   keep sequence.kind == XCORE_SEND_FRAME;

     
};

extend xbus_agent_u {
    keep logger.verbosity == FULL;
};
extend xserial_agent_u {
    keep logger.verbosity == FULL;
};

-- Control the XCore - program to read and write frames
extend MAIN vr_ad_sequence {

   -- Reflect all 3 input frames back to the output
   keep count == 3;
   keep sequence.kind == XCORE_XBUS_READ_WRITE;
    
   keep prevent_test_done == TRUE;

};


extend MAIN INIT_LINK xbus_master_sequence {
    body() @driver.clock is also {
        // Do nothing, just to see how the others wait for me to 
        // get to MAIN_TEST
        wait [100] * cycle;
        if driver.tf_get_domain_mgr().get_invocation_count(INIT_LINK) < 2 
                                                                  then {
            wait [80];
            message(TESTFLOW_EX, LOW, "Calling rerun_phase(RESET)");
            driver.tf_get_domain_mgr().rerun_phase(RESET);
        };
        
    };    

};


-- No virtaul sequence in this test, scneraio created by BFM sequences
extend MAIN MAIN_TEST xcore_combined_sequence {
    keep count == 0;
};
'>


 Debugging messages, to see how xserial waits for xbus to finish its reset


<'
extend sys {
    run() is also {
        specman("trace testflow");
    };
};

'>
