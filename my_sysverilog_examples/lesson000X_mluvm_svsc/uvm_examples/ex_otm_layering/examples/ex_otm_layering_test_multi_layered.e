/*----------------------------------------------------------    
File name   : ex_otm_layering_test_multi_layered.e
Title       : example test file 
Project     : one to many layering example
Created     : 2007
Description : Defines test using layered sequences
            : Starts several sequences in parallel: 
            :   4 sequences of the upper layer (packet) 
            :   3 sequences of the lower layer (ATM)
            : The sequences are constrained such that:
            :    - layered ATM sequence id 1 gets items from 
            :      three packet sequences 
            :    - layered ATM sequence id 2 gets items from 
            :      one packet sequence
            :    - ALL_RED frame sequence generates its own items
            :      (it is a low layer, but not a layered sequence)
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
           // id 1 layered scenario 
           {
               do LAYERED atm_sequence keeping {
                   .atm_id == 1;
                   .atm_header == 2;
               };
               message(HIGH,"ATM LAYERED1 done");
           };
           {
               do LAYERED_LONG packet_sequence keeping {
                   .upper_layer_id == 1;
               };  
               
               do LAYERED_SHORT packet_sequence keeping {
                   .upper_layer_id == 1;
               };  
               
               do LAYERED_LONG packet_sequence keeping {
                   .upper_layer_id == 1;
               };  
               
               message(HIGH,"PACKET LAYERED1 done");
           };
           // id 2 layered scenario 
           {
               do LAYERED atm_sequence keeping {
                   .atm_id == 2;
                   .atm_header == 3;
               };
               message(HIGH,"ATM LAYERED2 done");
           };
           {
               do LAYERED packet_sequence keeping {
                   .upper_layer_id == 2;
               };  
               message(HIGH,"PACKET LAYERED2 done");
           };
           // "independent" ATM sequence 
           {
               do ALL_RED atm_sequence;
               message(HIGH,"ATM UN-LAYERED done");
           };
       };
   };   
};


'>
