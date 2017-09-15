/*------------------------------------------------------------------------- 
File name   : test_1.e
Title       : XSerial eVC demo - example testcase file
Project     : XSerial eVC
Created     : 2008
Description : Example testcase file for demo purposes
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

extend XSERIAL_C MAIN MAIN_TEST  xserial_sequence {
    keep count == 10;
};

-- There are only three destination ports on the router - in this case
-- we want all frames sent to all ports to have port A as a destination.
-- This should load the router such that flow control operates.
extend xserial_frame_payload_s {
    keep destination == 0;
}; -- extend xserial_frame_payload_s

'>

