/*----------------------------------------------------------    
File name   : ex_oto_layering_test.e
Title       : example test file 
Project     : one to one layering example
Created     : 2007
Description : Defines test using layered sequences.
            : Start 4 sequences in parallel: 
            :   2 sequences of the upper layer (packet) 
            :   2 sequences of the lower layer (frame)
            : The sequences id numbers are contrained such that
            : each frame sequence is paired to one of the packet 
            : sequences.
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
                   .destination_address == 0x001100110011;
                   .source_address == 0x002200220022;    
               };
           };
           {
               do LAYERED packet_sequence keeping {
                   .upper_layer_id == 1;
               };  
           };
           {
               do LAYERED frame_sequence keeping {
                   .ll_id == 2;
                   .destination_address == 0x003300440055;
                   .source_address == 0x006600770088;    
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
