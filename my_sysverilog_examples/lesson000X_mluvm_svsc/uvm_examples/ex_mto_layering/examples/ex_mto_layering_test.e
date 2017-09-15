/*----------------------------------------------------------    
File name   : ex_mto_layering_test.e
Title       : example test file 
Project     : many to one layering example
Created     : 2007
Description : Defines test using layered sequences
            : Start 1 low layer sequence, and 10 upper layer
            : sequences. All id numbers are same, so the low
            : layer sequence gets its items from all the 10 
            : upper layer sequences.
Notes       : This is one of four layering examples: One to one, 
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 
 
<'
import ex_mto_layering/e/ex_mto_layering_top.e;
'>

   
<'

extend MAIN system_sequence {
   
   body() @driver.clock is only {

       all of {
           {
               do LAYERED ll_pkt_sequence keeping {
                   .ll_pkt_id == 1;
               };
           };
           {
               for i from 0 to 9 {
                   do LAYERED_LONG ul_pkt_sequence keeping {
                       .upper_layer_id == 1;
                   };
               };  
           };
       };
   };   
};


'>
