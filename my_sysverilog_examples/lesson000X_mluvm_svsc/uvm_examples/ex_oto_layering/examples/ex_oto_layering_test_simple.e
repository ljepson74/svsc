/*----------------------------------------------------------    
File name   : ex_oto_layering_test_simple.e
Title       : example test file 
Project     : one to one layering example
Created     : 2007
Description : Defines test using layered sequences
            : Start 2 sequences in parallel: 
            :   a sequence of the upper layer (packet) 
            :   a sequence of the lower layer (frame)
            : The id numbers are contrained to be the same
Notes       : This is one of four layering examples: One to one, 
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 

<'
import ex_oto_layering/e/ex_oto_layering_top.e;
'>

<'

extend MAIN system_sequence {

    body() @driver.clock is only {

       all of {
           {
               do LAYERED frame_sequence keeping {
                   .ll_id == 1;
                   .destination_address == 0xAABBCCDDEEFF;
                   .source_address == 0x001122334455;
               };
           };
           {
               do LAYERED packet_sequence keeping {
                   .upper_layer_id == 1;
               };  
           };
       };
   };   
};


'>
