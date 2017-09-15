/*----------------------------------------------------------    
File name   : ex_oto_layering_frame_seq_lib.e
Title       : frame sequence library 
Project     : one to one layering example
Created     : 2007
Description : Defines reusable frame sequences for usage in tests
Notes       : This is one of four layering examples: One to one,
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 


  

<'
extend ex_oto_layering_frame_sequence_kind: [LAYERED];

extend LAYERED ex_oto_layering_frame_sequence {
    ll_id: uint; // used for synchronizing with upper layer
    destination_address : uint (bits:48); 
    source_address : uint (bits:48); 
    !frame_payload: list of byte;
    
    is_relevant() : bool is {
        result = driver.ll_check_do_available$(ll_id);
    };
        
    body() @driver.clock is only{

        var continue_work: bool;
        continue_work = TRUE; 
        
        while continue_work { // while there are more upper layer items
            first of {
                {
                    
                    driver.wait_for_grant(me);
                    
                    var layering_struct: layering_data_struct_s;
                    layering_struct = driver.get_item_from_upper_layer(ll_id);
                    // gets upper layer item or stalls when there is none          
                    frame_payload = pack(NULL,layering_struct.data);
                    
                    gen frame keeping {
                        .payload == frame_payload;
                        .destination_address == destination_address;
                        .source_address == source_address;
                    };
                    
                    driver.deliver_item(frame);
                    
                };
                {
                    // time out for upper layer items (can be increased or 
                    // decreased upon need) 
                    // enables stop_run from virtual sequence
                    wait [2000];
                    continue_work = FALSE;
                };
            };
        };
    };
};

'>

<'
// this is an example for regular (non layered) frame sequence. 
// it can be called with no limitations during layered tests.

extend ex_oto_layering_frame_sequence_kind: [ALL_RED];
extend ALL_RED ex_oto_layering_frame_sequence {

    count: int[1..10];
    
    body() @driver.clock is {
        for i from 1 to count {
            do frame keeping {.color == RED};
        };
    };
};

'>

