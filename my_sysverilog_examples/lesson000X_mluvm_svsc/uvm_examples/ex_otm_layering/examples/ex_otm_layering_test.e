/*----------------------------------------------------------    
File name   : ex_otm_layering_test.e
Title       : example test file 
Project     : one to many layering example
Created     : 2007
Description : Defines test using layered sequences
            : Starts 2 ATM sequences, and 2 packet sequences.
            : The sequences id numbers are constrained such that
            : each ATM sequence gets its item from one of the 
            : packet sequences.
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
           {
               do LAYERED atm_sequence keeping {
                   .atm_id == 2;
                   .atm_header == 3;
               };
           };
           {
               do LAYERED packet_sequence keeping {
                   .upper_layer_id == 2;
               };  
           };
       };
   };   
};


'>
