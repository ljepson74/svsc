/*------------------------------------------------------------------------- 
File name   : test_reconfiguration.e
Title       : XSerial demo of multiple configurations
Project     : XSerial eVC
Created     : 2008
Description : This file demonstrates the ability of the eVC to cope with
            : multiple configurations. 
            :  
            : Call xserial_env configure method several times, each time
            : with different set of parameters, and check the result.
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


// unit configure itself
extend XSERIAL_A xserial_env_u {
    run() is also {
         message(LOW, "Config mode to SLOW");
        //            ----------------------------------------
        uvm_configure 1 me {mode} 
                               {xserial_mode_t'SLOW};
               
        // Check:
        check that config.params.mode == SLOW else
          dut_error("1st configuration failed, config.params.mode == ",
                    config.params.mode);         
    };   
};


// unit configures sub units
extend sys {
    run() is also {
         message(LOW, "Config XSERIAL_1 mode to NORMAL");
        //            ----------------------------------------
        uvm_configure 2 xserial_evcs[1] {mode} {xserial_mode_t'NORMAL};
               
        // Check:
        check that xserial_evcs[1].config.params.mode == NORMAL else
          dut_error("2nd configuration failed, ",
                    "xserial_evcs[1].config.params.mode == ",
                    xserial_evcs[1].config.params.mode);    
        
         message(LOW, "Config XSERIAL_2 mode to FAST");
        //            ----------------------------------------
        uvm_configure 3 xserial_evcs[2] {mode} {xserial_mode_t'FAST};
               
        // Check:
        check that xserial_evcs[2].config.params.mode == FAST else
          dut_error("3rd configuration failed, ",
                    "xserial_evcs[2].config.params.mode == ",
                    xserial_evcs[2].config.params.mode);         

    
    };   
    
};

'>
