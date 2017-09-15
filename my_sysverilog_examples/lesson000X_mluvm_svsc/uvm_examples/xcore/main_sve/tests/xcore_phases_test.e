----------------------------------------------------------------------------
----------------------------------------------------------------------------

File name    : xcore_phases_test.e
Title        : Testflow Demonstrated
Project      : XCore eVC
Created On   : 2008
Description  : 
             : Dummy activities, demoing how the components go from phase 
             : to phase, and wait when required - xserial and xcore depend
             : on xbus's reset,  the three domain synch on MAIN_TEST and 
             : POST_TEST
----------------------------------------------------------------------------
>>>>>>>>>>>>>>>>>>>>>>>>>>> COPYRIGHT NOTICE <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
----------------------------------------------------------------------------
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
----------------------------------------------------------------------------

<'

import xcore/main_sve/main_sve_config;
import setup_test;


extend MASTER xbus_agent_u {
    tf_env_setup() @tf_phase_clock is also {
        wait [200] * cycle;
    };
    tf_hard_reset() @tf_phase_clock is also {
        wait [400] * cycle;
    };
    tf_reset() @tf_phase_clock is also {
        wait [200] * cycle;
    };
    tf_init_dut() @tf_phase_clock is also {
        wait [400] * cycle;
    };
    tf_init_link() @tf_phase_clock is also {
        wait [400] * cycle;
    };
    tf_main_test() @tf_phase_clock is also {
        wait [100] * cycle;
    };
    tf_finish_test() @tf_phase_clock is also {
        wait [100] * cycle;
    };
    tf_post_test() @tf_phase_clock is also {
        wait [100] * cycle;
    };   
};

       
extend MAIN RESET xcore_combined_sequence {
    body() @driver.clock is also {
        wait [50] * cycle;
    };
};
extend MAIN MAIN_TEST xcore_combined_sequence {
    body() @driver.clock is only {
        wait [50] * cycle;
    };
};

'>

 Debugging messages, to see how the components proceed from phase to phase




<'

extend xbus_agent_u {
    keep logger.verbosity == FULL;
};
extend xserial_agent_u {
    keep logger.verbosity == FULL;
};

extend sys {
    run() is also {
        specman("trace testflow");
    };
};



'>
