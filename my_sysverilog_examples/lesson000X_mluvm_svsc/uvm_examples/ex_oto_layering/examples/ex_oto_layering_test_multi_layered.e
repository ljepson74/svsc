/*----------------------------------------------------------    
File name   : ex_oto_layering_test_multi_layered.e
Title       : example test file 
Project     : one to one layering example
Created     : 2007
Description : Defines test using layered sequences
            : Starts several sequences in parallel: 
            :   4 sequences of the upper layer (packet) 
            :   3 sequences of the lower layer (frame)
            : The sequences are constrained such that:
            :    - layered frame sequence id 1 gets items from 
            :      three packet sequences 
            :    - layered frame sequence id 2 gets items from 
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
import ex_oto_layering/e/ex_oto_layering_top.e;
'>

<'

extend MAIN system_sequence {
   
   body() @driver.clock is only {

       all of {
           // id 1 layered scenario 
           {
               do LAYERED frame_sequence keeping {
                   .ll_id == 1;
                   .destination_address == 0x110011001100;
                   .source_address == 0x220022002200;
               };
               message(MEDIUM, "frame LAYERED1 done");
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
               
               message(MEDIUM, "PACKET LAYERED1 done");
           };
           // id 2 layered scenario 
           {
               do LAYERED frame_sequence keeping {
                   .ll_id == 2;
                   .destination_address == 0x330033003300;
                   .source_address == 0x440044004400;
               };
               message(MEDIUM,"frame LAYERED2 done");
           };
           {
               do LAYERED packet_sequence keeping {
                   .upper_layer_id == 2;
               };  
               message(MEDIUM,"PACKET LAYERED2 done");
           };
           // "independent" frame sequence
           {
               do ALL_RED frame_sequence;
               message(MEDIUM,"frame UN-LAYERED done");
           };
       };
   };   
};


'>
