/*----------------------------------------------------------    
File name   : ex_mto_layering_ll_pkt_seq_lib.e
Title       : packet sequence library 
Project     : many to one layering example
Created     : 2007
Description : Defines reusable ul pkt sequences for usage in tests
Notes       : This is one of four layering examples: One to one, 
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 
 

<'
define LL_TIMEOUT 4000;

extend ex_mto_layering_ll_pkt_sequence_kind: [LAYERED];

extend LAYERED ex_mto_layering_ll_pkt_sequence {
    max_length: uint;
    keep soft max_length in [LL_MIN_PKT_LEN..LL_MAX_PKT_LEN];
    ll_pkt_id: uint; // used for synchronizing with upper layer

    body() @driver.clock is only{

        var continue_work: bool;
        continue_work = TRUE; 
        var tmp_payload : list of byte;
        while continue_work { // while there are more upper layer items
            // continue_work is set to FALSE upon timeout
            first of {
                {
                    var layering_struct: layering_data_struct_s;
                    var remaining_bytes : uint;
                    remaining_bytes = max_length - tmp_payload.size();
                    layering_struct = get_item_from_upper_layer(
                        ll_pkt_id, remaining_bytes);
                    // gets upper layer item or stalls when there is none
                    if layering_struct.data.size() == 0 then {
                        // signal to encapsulate and send current payload 
                        do ll_pkt keeping {
                            .payload == tmp_payload;
                        };
                        tmp_payload.clear();
                    } else {
                        // continue payload accumulation
                        tmp_payload.add(layering_struct.data);
                    };
                };
                {
                    // time out for upper layer items (can be increased or 
                    // decreased upon need) should be much bigger then 
                    // typical accumulation time. enables stop_run from virtual
                    // sequence
                    wait [LL_TIMEOUT];
                    if tmp_payload.size() > 0 then {
                        // send any leftovers from upper layer
                        do ll_pkt keeping {
                            .payload == tmp_payload;
                        };
                    };    
                    continue_work = FALSE;
                };
            };
        };
    };
};

'>

<'
// this is an example for regular (non layered) ll_pkt sequence. 
// it can be called with no limitations during layered tests.

extend ex_mto_layering_ll_pkt_sequence_kind: [ALL_RED];
extend ALL_RED ex_mto_layering_ll_pkt_sequence {

    count: int[1..10];
    
    body() @driver.clock is {
        for i from 1 to count {
            do ll_pkt keeping {.color == RED};
        };
    };
};

'>


