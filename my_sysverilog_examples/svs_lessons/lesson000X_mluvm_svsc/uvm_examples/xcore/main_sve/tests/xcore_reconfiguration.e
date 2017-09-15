----------------------------------------------------------------------------
----------------------------------------------------------------------------

File name    : xcore_reconfiguration.e
Title        : Reconfiguration test
Project      : XCore eVC
Created On   : 2008
Description  : Test scneario:
             :
             : This file demonstrates the ability of the eVC to cope with
             : multiple configurations. Each time it should propagate
             : config info to sub-components
             :  
             : Call xbus_env configure method several times, each time
             : with different set of parameters, and check the result.
----------------------------------------------------------------------------
>>>>>>>>>>>>>>>>>>>>>>>>>>> COPYRIGHT NOTICE <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
----------------------------------------------------------------------------
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
All rights reserved worldwide
----------------------------------------------------------------------------

<'

import xcore/main_sve/main_sve_config;
import setup_test;


-- Main scenario:
-- configure the xcore env several times during the run
-- since the env participates here in defining test scenario - add it to 
-- the testflow
extend xcore_env_u  {
    
    tf_main_test() @tf_phase_clock is also {
        // Start tet scneraio
        start reconfig_during_the_run();
        
        // Register the thread as running only in MAIN_TEST, blocking.
        // The domain will not proceed to next phase, before this TCM is over.
        tf_get_domain_mgr().register_thread_by_name(me, "reconfig_during_the_run", 
                                                    MAIN_TEST, TRUE);
  
    };
    
    reconfig_during_the_run() @tf_phase_clock is {
        
        wait [10] * cycle;
        message(LOW, "Config XCORE mode to NORMAL, Speed to 100");
        //            ----------------------------------------
        uvm_configure 1 me {mode; max_speed} {xcore_mode_t'NORMAL; 100};
               
        // Check:
        check that config.params.mode == NORMAL else
          dut_error("2nd configuration failed, ",
                    "config.params.mode == ",
                    config.params.mode);    
        check that config.params.max_speed == 100 else
          dut_error("2nd configuration failed, ",
                    "config.params.max_speed == ",
                    config.params.max_speed);    
       
        check that xserial_evc.config.params.mode == SLOW else
          dut_error("2nd configuration failed, ",
                    "xserial_evc.config.params.mode == ",
                    xserial_evc.config.params.mode);    
        // -------------------------------------------------------
        wait [10] * cycle;
        message(LOW, "Config XCORE mode to NORMAL, Speed to 1000");
        //            ----------------------------------------
        uvm_configure 1 me {mode; max_speed} {xcore_mode_t'NORMAL; 1000};
                   
        // Check:
        check that config.params.mode == NORMAL else
          dut_error("2nd configuration failed, ",
                    "config.params.mode == ",
                    config.params.mode);    
        check that config.params.max_speed == 1000 else
          dut_error("2nd configuration failed, ",
                    "config.params.max_speed == ",
                    config.params.max_speed);    
       
        check that xserial_evc.config.params.mode == NORMAL else
          dut_error("2nd configuration failed, ",
                    "xserial_evc.config.params.mode == ",
                    xserial_evc.config.params.mode);    
        // -------------------------------------------------------
        wait [10] * cycle;
        message(LOW, "Config XCORE mode to FULL_SPEED");
        //            ----------------------------------------
        uvm_configure 1 me {mode} {xcore_mode_t'FULL_SPEED };
               
        // Check:
        check that config.params.mode == FULL_SPEED else
          dut_error("2nd configuration failed, ",
                    "config.params.mode == ",
                    config.params.mode);    
        check that config.params.max_speed == 1000 else
          dut_error("2nd configuration failed, ",
                    "config.params.max_speed == ",
                    config.params.max_speed);    
       
        check that xserial_evc.config.params.mode == FAST else
          dut_error("2nd configuration failed, ",
                    "xserial_evc.config.params.mode == ",
                    xserial_evc.config.params.mode);    
        // -------------------------------------------------------
        wait [10] * cycle;
        message(LOW, "Config XCORE mode to FULL_SPEED, Speed to 37");
        //            ----------------------------------------
        uvm_configure 1 me {mode; max_speed} {xcore_mode_t'FULL_SPEED; 37};
               
        // Check:
        check that config.params.mode == FULL_SPEED else
          dut_error("2nd configuration failed, ",
                    "config.params.mode == ",
                    config.params.mode);    
        check that config.params.max_speed == 37 else
          dut_error("2nd configuration failed, ",
                    "config.params.max_speed == ",
                    config.params.max_speed);    
       
        check that xserial_evc.config.params.mode == FAST else
          dut_error("2nd configuration failed, ",
                    "xserial_evc.config.params.mode == ",
                    xserial_evc.config.params.mode);    
        // -------------------------------------------------------

        // TCM is over - unregister, so domain may proceed to next phase
        tf_get_domain_mgr().unregister_thread();
    };
};

// initial values
extend xcore_env_config_params_s {
    keep soft mode == FULL_SPEED;
    keep soft max_speed == 1024;
};

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

-- No virtaul sequence in this test, scneraio created by BFM sequences
extend MAIN MAIN_TEST xcore_combined_sequence {
    keep count == 0;
};
'>
