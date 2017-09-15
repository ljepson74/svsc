/*------------------------------------------------------------------------- 
File name   : test_item_constraint.e
Title       : XSerial eVC demo - example testcase file
Project     : XSerial eVC
Created     : 2008
Description : Example file for item constraint demonstration. MAIN is calling 
              MID_LAYER sequence which in turn calls LOW_LAYER which does an 
              item. using the item constraint macro, we influence the item
              generation from a top layer sequence.
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
    
}; 

extend xserial_sequence_kind:[MID_LAYER, LOW_LAYER];

extend XSERIAL_A MID_LAYER MAIN_TEST xserial_sequence {
    !sub_seq: XSERIAL_A LOW_LAYER MAIN_TEST xserial_sequence;
    body() @driver.clock is only {
        do sub_seq;
    };
};

extend XSERIAL_A LOW_LAYER MAIN_TEST xserial_sequence {
    !item: TX xserial_frame_s;
    body() @driver.clock is only {
        do item;
    };
};


// set a constraint on the item that is generated in a low layer sequence 
item_constraint TX xserial_frame_s.set_payload {
    payload.frame_format == DATA; //|block of constraints
    payload.DATA'data == 5;       //| 
};



extend XSERIAL_A MAIN MAIN_TEST xserial_sequence {
    !sub_seq: XSERIAL_A MID_LAYER MAIN_TEST xserial_sequence;
    
    body() @driver.clock is only {
        // activating the sequence with the keyword results in the block 
        // of constraints being executed during item generation.
        do set_payload sub_seq;
    };
};


extend XSERIAL_B MAIN MAIN_TEST xserial_sequence {
    keep count == 0;
};
extend XSERIAL_C MAIN MAIN_TEST xserial_sequence {
    keep count == 0;
};

-- There are only three destination ports on the router - in this case
-- we want all frames sent to all ports to have port A as a destination.
-- This should load the router such that flow control operates.
extend xserial_frame_payload_s {
    keep destination == 0;
}; -- extend xserial_frame_payload_s

'>

