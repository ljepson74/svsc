/*------------------------------------------------------------------------- 
File name   : xcore_config.e
Title       : XCore configuration
Project     : XCore eVC
Created     : 2008
Description : This file configures the top level unit of the eVC
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide.

-------------------------------------------------------------------------*/ 

<'

package cdn_xcore;


extend xcore_virtual_driver {
    keep soft tf_domain == XCORE_TF;
};


extend sys {
   
    
    connect_pointers() is also {
        
        // Reset of the DUT is performed by the xbus Master, so the other 
        // domains - xserial and xcore - should not proceed beyond RESET 
        // before the xbus is done with all initial phases (INIT_LINK is 
        // the last phase before MAIN_TEST)
        tf_add_dependency(XSERIAL_TF, RESET, XBUS_TF, INIT_LINK);
        tf_add_dependency(XCORE_TF,   RESET, XBUS_TF, INIT_LINK);
        
        // Define dependencies: The three domains should synchronize on
        //  MAIN_TEST and POST_TEST
        //  - do not start main test scenario before all are out of reset,
        // do not proceed to post test activities before all done with their
        // scenario
        tf_add_mut_dependency({XBUS_TF;XSERIAL_TF;XCORE_TF}, MAIN_TEST);
        tf_add_mut_dependency({XBUS_TF;XSERIAL_TF;XCORE_TF}, POST_TEST);
    };
};

'>
