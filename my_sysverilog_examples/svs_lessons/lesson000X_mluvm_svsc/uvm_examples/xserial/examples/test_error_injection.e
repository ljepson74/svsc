/*------------------------------------------------------------------------- 
File name   : test_error_injection.e
Title       : XSerial eVC demo - example testcase file
Project     : XSerial eVC
Created     : 2008
Description : Example testcase file for demo purposes
Notes       : This test case introduces bad format and parity errors randomly
            : on the output of the XSERIAL_A instance of the XSerial eVC.
            : Note that the DUT discards any frames with parity errors (and
            : flags this using the appropriate port error signal).
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

-- Each possible error has a 30% probability in each frame.
extend XSERIAL_A TX xserial_frame_s {
    keep soft payload.frame_format == select {
        30 : UNDEFINED;
        70 : DATA;
    };    
    keep soft bad_parity == select {
        30 : TRUE;
        70 : FALSE;
    };
};

-- We are expecting errors, so turn off all protocol checkers
extend xserial_agent_u {
    keep check_tx_protocol == FALSE;
    keep check_rx_protocol == FALSE;
};

'>

