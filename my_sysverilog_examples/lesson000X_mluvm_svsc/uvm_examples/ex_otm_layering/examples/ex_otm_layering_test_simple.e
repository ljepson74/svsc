/*----------------------------------------------------------    
File name   : ex_otm_layering_test_simple.e
Title       : example test file 
Project     : one to many layering example
Created     : 2007
Description : Defines test using layered sequences
            : Two sequences, one ATM (lower layer) sequence, getting 
            : its items from one Packet (upper layer) sequence.
Notes       : This is one of four layering examples: One to one,
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 
    
<'
import ex_otm_layering/e/ex_otm_layering_top.e;
'>

<'

extend MAIN system_sequence {
   
   body() @driver.clock is only {

       all of {
           {
               do LAYERED atm_sequence keeping {
                   .atm_id == 1;
                   .atm_header == 2;
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
