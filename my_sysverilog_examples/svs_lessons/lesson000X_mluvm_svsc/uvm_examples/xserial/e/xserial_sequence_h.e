/*------------------------------------------------------------------------- 
File name   : xserial_sequence_h.e
Title       : Xserial Sequence
Project     : XSerial eVC
Created     : 2008
Description : This file implements sequences.
Notes       : See Sequence documentation for more information about how
            : sequences work.
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
-------------------------------------------------------------------------*/ 

<'

package cdn_xserial;


-- This type enumerates the logical names of each instance of the eVC in the
-- Verification Environment.
type xserial_env_name_t : [];


-- This creates a sub-type of the frame struct that has additional
-- information relating to generation of frames by the sequence
-- interface.
extend TX xserial_frame_s {

    -- This field can be used to sub-type the TX frame according to the 
    -- eVC instance that is sending it.
    name : xserial_env_name_t;
        keep name == read_only(driver).name;
    
    -- This field controls the delay before transmission of this frame in
    -- clock cycles - timed from the end of the previous frame.
    transmit_delay : uint;
        keep soft transmit_delay in [5..20];

}; -- extend TX xserial_frame_s


-- This is the generic sequence struct for transmitting frames from the eVC.
sequence xserial_sequence using 
    testflow = TRUE,
    item=TX xserial_frame_s, 
    created_driver=xserial_driver_u;


-- Provide extensions to the sequence driver so that the driver, 
-- the sequence and the sequence items can all be sub-typed by the 
-- instance name of the eVC.
extend xserial_driver_u {
    keep soft tf_domain == XSERIAL_TF;

    -- This field holds the name of the env this driver is contained in.
    name : xserial_env_name_t;
};


extend xserial_sequence {

    -- This field allows sequences to be sub-typed on the name of the env.
    name : xserial_env_name_t;
        keep name == read_only(driver).name;
 
    -- This is a utility field for basic sequences. This allows the user to
    -- do "do frame ...".
    !frame: TX xserial_frame_s;

    // Cover the sequence. 
    // Ignore the pre-defined kinds, they do not add info to the coverage
    cover ended is {
        item kind using ignore = (kind == RANDOM or
                                  kind == SIMPLE or
                                  kind == MAIN);
    }; 
    
}; -- extend xserial_sequence


'>
