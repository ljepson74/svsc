/*----------------------------------------------------------    
File name   : ex_mtm_layering_system_seq_lib.e
Title       : system level sequence library file 
Project     : many to many layering example
Created     : 2007
Description : Defines reusable system level sequences 
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

<'

// Start all the sequences good for most test scenarios

extend system_sequence_kind: [DEFAULT_SEQS];

extend DEFAULT_SEQS system_sequence {
    body() @driver.clock is {
        // The following four sequences are required for most 
        // of the tests.
        // All of them work in endless loops, 

        // 1) start the lower layer sequence - keeps getting items
        // from the layer above it (the mediator layer)
        gen LAYERED ll_pkt_sequence keeping {
            .ml_driver == driver.ml_pkt_driver;    
        };      
        ll_pkt_sequence.start_sequence();
        
        // 2) start header mediating sequence - 
        // keeps getting header items from the upper layer layer
        gen HEADER LAYERED ml_header_sequence keeping {
            .ml_pkt_id == 1;
        };
        
        // connect the method port to upper layer
        ml_header_sequence.get_item_layer_transfer = 
            driver.ml_pkt_driver.get_item_layer_transfers[1];
        ml_header_sequence.start_sequence();
        
        // 3) start payload mediating sequence  - 
        // keeps getting payload items from the upper layer layer
        gen PAYLOAD LAYERED ml_pkt_sequence keeping {
            .ml_pkt_id == 1;
        };
        // connect the method port to upper layer
        ml_pkt_sequence.get_item_layer_transfer = 
            driver.ml_pkt_driver.get_item_layer_transfers[0];
        ml_pkt_sequence.start_sequence();
        
        // 4) start header upper sequence - keeps generating headers
        gen HEADER ul_header_sequence keeping {
            .upper_layer_id == 1;
        };
        ul_header_sequence.start_sequence();
    };
};
     

'>

