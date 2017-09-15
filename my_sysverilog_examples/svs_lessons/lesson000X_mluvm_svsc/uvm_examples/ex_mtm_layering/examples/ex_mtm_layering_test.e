/*----------------------------------------------------------    
File name   : ex_mtm_layering_test.e
Title       : example test file 
Project     : many to many layering example
Created     : 2007
Description : Defines test using layered sequences.
            : Starts the DEFAULT_SEQS system sequence, which starts
            : all default layered sequences. All low and mediator 
            : layers sequences run, waiting for items from the upper
            : layer.
            : Starts 10 sequences of the upper layer. They will 
            : be handled by the sequecnes startd by the DEFAULT_SEQS
            : system sequence.
Notes       : This is one of four layering examples: One to one, 
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 

<'
import ex_mtm_layering/e/ex_mtm_layering_top.e;
'>


<'

extend MAIN system_sequence {
   body() @driver.clock is only {
       
       do DEFAULT_SEQS system_sequence;       
       
       // start upper layer payload sequence
       for i from 0 to 9 {
           do ul_pkt_sequence keeping {
               .upper_layer_id == 1;
               .kind in {EXACT; LAYERED};
           };
       };
   };   
};


'>
