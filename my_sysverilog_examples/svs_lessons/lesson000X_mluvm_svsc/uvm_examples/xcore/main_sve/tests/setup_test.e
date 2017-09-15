----------------------------------------------------------------------------
----------------------------------------------------------------------------

File name    : setup_test.e
Title        : XCore eVC demo - example test setup file
Project      : XCore
Created On   : 2008
Description  : 
Notes        :  
----------------------------------------------------------------------------
>>>>>>>>>>>>>>>>>>>>>>>>>>> COPYRIGHT NOTICE <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
----------------------------------------------------------------------------
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
----------------------------------------------------------------------------

<'

extend sys {
    setup() is also {
        set_config(print, radix, hex);
        set_config(run, tick_max, MAX_INT);
    };
   init() is also {
      set_config(cover,show_instances_only, TRUE);
   };
};


extend MAIN MAIN_TEST xbus_master_sequence {
   
    keep soft sequence.kind in [XCORE_WRITE_FRAME, 
                               XCORE_READ_FRAME, 
                               XCORE_READ_WRITE_FRAME];

    
}; 


extend MAIN vr_ad_sequence {
    keep soft sequence.kind == XCORE_XBUS_READ_WRITE;    
}; 

'>
   
   
   
