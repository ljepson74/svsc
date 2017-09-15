----------------------------------------------------------------------------
----------------------------------------------------------------------------

File name    : xcore_virtual_seq_doing_items_test.e
Title        : XCore eVC test - virtual Seq Doing Items
Project      : XCore eVC
Created On   : 2008
Description  : Demostrate the ability of a virtual sequence to send 
             : items (of other sequences)
             : 
Notes        : When doing items from the virtual sequence, one has to 
             : know the details of the i/f protocol. This is simple in
             : the case of the XSerial - just generate a legal packet.
             : It is more complicated for the XBus, because the XBus
             : protocol requires accessing specific addresses in 
             : specific conditions. No sense for implementing this
             : protocol in the virtual sequence, so it does XBus predefined
             : sequences
----------------------------------------------------------------------------
>>>>>>>>>>>>>>>>>>>>>>>>>>> COPYRIGHT NOTICE <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
----------------------------------------------------------------------------
Copyright (c) 2009 Cadence Design Systems,Inc.
  All rights reserved worldwide
----------------------------------------------------------------------------

<'

import xcore/main_sve/main_sve_config;


extend MAIN MAIN_TEST xcore_combined_sequence {
    !xbus_read_frame_seq :  XCORE_READ_FRAME xbus_master_sequence;
    !xserial_frame :  TX xserial_frame_s;
    
    
    body() @driver.clock is only {
    
        for i from 0 to 3 {
            // Doing an item:
            do xserial_frame on driver.xserial_driver;
            
            // Doing a sequence:
            do xbus_read_frame_seq keeping {.driver == driver.xbus_driver};
        };
        // Note - the item can also be sent using deliver_item. 
        gen xserial_frame keeping {.driver == driver.xserial_driver};
        driver.xserial_driver.wait_for_grant(me);
        driver.xserial_driver.deliver_item(xserial_frame);
        
        do xbus_read_frame_seq keeping {.driver == driver.xbus_driver};
    }; 

};


'>

