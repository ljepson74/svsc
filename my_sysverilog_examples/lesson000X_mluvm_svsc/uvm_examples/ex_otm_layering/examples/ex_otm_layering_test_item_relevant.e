/*----------------------------------------------------------    
File name    : ex_otm_layering_test_item_relevant.e
Title        : example test file 
Project      : one to many layering example
Created      : 2007
Description  : Defines test using layered sequences. A dummy DUT 
             : imitates a back-pressure, for demonstrating the item
             : post generation is_relevant
Notes        : This is one of four layering examples: One to one, 
             : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 
 
<'
import ex_otm_layering/e/ex_otm_layering_top.e;
'>


Dummy DUT : imitate a back-pressure

<'
extend dut_u {
    back_pressure_value: uint(bits:40);
    run() is also {
        start back_pressure_process();
    };
    back_pressure_process() @sys.any is {
        while TRUE {
            gen back_pressure_value keeping {
                it in [2..3];
            };
            back_pressure$ = back_pressure_value;
            wait [1];
        };
    };
};
'>


Time consuming generation:

For better demonstration of the item post generation is_relevant,
imitate time consuming generation. In the time the item is being 
generation, back pressure status might be modified (and hence - 
it_relevant status will change).

<'
extend ex_otm_layering_atm_sequence {
    pre_do(is_item: bool) @sys.any is also {
        if is_item then {
            wait[5]; 
            // ... perform time consuming generation ...
        };
    };
};


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
               for i from 0 to 3 {
                   do LAYERED packet_sequence keeping {
                       .upper_layer_id == 1;
                   };  
               };
           };
       };
   };   
};


'>
