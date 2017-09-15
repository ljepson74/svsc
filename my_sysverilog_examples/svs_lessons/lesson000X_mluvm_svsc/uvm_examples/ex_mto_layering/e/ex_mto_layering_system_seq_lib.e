/*----------------------------------------------------------    
File name   : ex_mto_layering_system_seq_lib.e
Title       : system level sequence library file 
Project     : many to one layering example
Created     : 2007
Description : Defines reusable system level sequences for usage in tests
Notes       : This is one of four layering examples: One to one, 
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 

 
<'

// set stop condition for the test
extend MAIN system_sequence {
   pre_body() @sys.any is first {
       driver.raise_objection(TEST_DONE);
   };
   
   post_body() @sys.any is also {
      wait [20] * cycle @driver.clock;
      driver.drop_objection(TEST_DONE);
   };
};


'>
