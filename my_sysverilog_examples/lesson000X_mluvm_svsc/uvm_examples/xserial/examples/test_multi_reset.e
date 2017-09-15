/*------------------------------------------------------------------------- 
File name   : test_multi_reset.e
Title       : XSerial demo of multiple resets
Project     : XSerial eVC
Created     : 2008
Description : Example testcase file for demo purposes - demonstrates
            : multiple resets.
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide.
----------------------------------------------------------------------------*/ 

<'

-- import the eVC configuration file (which in turn imports the XSerial eVC)
import xserial/examples/xserial_config;

extend sys {

    setup() is also {
        -- Print in hexadecimal by default
        set_config(print, radix, hex);
    };
    
}; -- extend sys

extend XSERIAL_A MAIN MAIN_TEST xserial_sequence {
    keep count == 30;
};

extend XSERIAL_B MAIN MAIN_TEST xserial_sequence {
    keep count == 20;
};

extend XSERIAL_C MAIN MAIN_TEST xserial_sequence {
    keep count == 10;
};

-- There are only three destination ports on the router - in this case
-- we want all frames sent to all ports to have port A as a destination.
-- This should load the router such that flow control operates.
extend xserial_frame_payload_s {
    keep destination == 0;
}; -- extend xserial_frame_payload_s



extend xserial_env_u {
    
    // One of the envs resets the environment during the run
    when XSERIAL_A xserial_env_u {
    do_extra_reset() @sys.any is {
        wait delay(100 us);
        agent.sig_reset$ = 1;
        wait [5];
        agent.sig_reset$ = 0;
        
        message(LOW, "Calling rerun_phase(RESET)");
        agent.tf_get_domain_mgr().rerun_phase(RESET);
     }; -- do_extra_reset()
    
    run() is also {
        start do_extra_reset();
    }; -- run()
        
    };
    
    
    event device_reset is cycle @agent.reset_start;
    
    on device_reset {
        // Inform the verification env about the reset
        agent.tf_get_domain_mgr().rerun_phase(RESET);
    };
};


'>


Debugging messages, seeing how moving from phase to phase


<'

extend xserial_agent_u {
    keep logger.verbosity == FULL;
};

extend sys {
    run() is also {
        specman("trace testflow");
    };
};

   
'>
