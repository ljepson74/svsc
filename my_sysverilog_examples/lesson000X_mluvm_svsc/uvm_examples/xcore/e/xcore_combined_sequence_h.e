/*------------------------------------------------------------------------- 
File name   : xcore_combined_sequence_h.e
Title       : Sequence definition
Project     : XCore eVC
Created     : 2008
Description : Sequences accessing XCore via XBus and XSerial
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide.

-------------------------------------------------------------------------*/ 

<'
package cdn_xcore;
'>
   
<'
sequence xcore_combined_sequence using testflow = TRUE, created_driver = xcore_virtual_driver;


extend xcore_combined_sequence {

    !regs_sequence    : vr_ad_sequence;
    !xserial_sequence : xserial_sequence;
    !xbus_sequence    : xbus_master_sequence;
    
    keep regs_sequence.driver == driver.xcore_regs_driver;
    keep xserial_sequence.driver == driver.xserial_driver;
    keep xbus_sequence.driver == driver.xbus_driver;
    

    // Cover the sequence. 
    // Ignore the pre-defined kinds, they do not add info to the coverage
    cover ended is {
        item kind using ignore = (kind == RANDOM or
                                  kind == MAIN);
    }; 
  
}; -- extend xcore...


extend MAIN xcore_combined_sequence {
   
   -- If this field is TRUE (the default), then an objection to TEST_DONE
   -- is raised for the duration of the MAIN sequence. If this field is FALSE
   -- then the MAIN sequence does not contribute to the determination of
   -- end-of-test.
   prevent_test_done : bool;
      keep soft prevent_test_done == FALSE;
   

};

extend MAIN ENV_SETUP xcore_combined_sequence {

       -- Raise an objection to TEST_DONE whenever a MAIN sequence is started.
    pre_body() @sys.any is first {
        message(TESTFLOW_EX, LOW, "MAIN ENV_SETUP sequence started");
        driver.raise_objection(TEST_DONE);
    }; -- pre_body()
};
extend MAIN POST_TEST xcore_combined_sequence {

    -- Drop the objection to TEST_DONE after the MAIN sequence ends.
    post_body() @sys.any is also {
        message(TESTFLOW_EX, LOW, "MAIN POST_TEST sequence finished");
        driver.drop_objection(TEST_DONE);
    }; -- post_body()
    
    
}; -- extend virtual_...

extend xcore_virtual_driver {
   !xcore_regs_driver    : vr_ad_sequence_driver;
   !xserial_driver       : xserial_driver_u;
   !xbus_driver          : xbus_master_driver_u;
   
   event clock is only @sys.any;

   get_sub_drivers(): list of any_sequence_driver is {
      return ({xcore_regs_driver; xserial_driver; xbus_driver});
   }; -- get_sub_drivers...

}; -- extend xcore_vi...

'>

    
