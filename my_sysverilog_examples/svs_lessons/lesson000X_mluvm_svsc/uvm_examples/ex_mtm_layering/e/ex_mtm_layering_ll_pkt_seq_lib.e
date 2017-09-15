
/*----------------------------------------------------------    
File name   : ex_mtm_layering_ll_pkt_seq_lib.e
Title       : packet sequence library 
Project     : many to many layering example
Created     : 2007
Description : Defines reusable ll pkt sequences for usage in tests
Notes       : This is one of four layering examples: One to one, 
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 


<'
define LL_PKT_LEN 3000;

// typically this is the only sequence that is used in the ll env. sometimes 
// there are special ll pkt transactios and in these cases they must be 
// synchronized with the regular flow
extend ex_mtm_layering_ll_pkt_sequence_kind: [LAYERED];

extend LAYERED ex_mtm_layering_ll_pkt_sequence {
    
    ml_driver: ex_mtm_layering_ml_pkt_driver_u; 
    // the interface to receive processed
    // ul objects (packets or headers)

    ll_pkt_length: uint;
    keep soft ll_pkt_length == LL_PKT_LEN;
    
    body() @driver.clock is only{
        var timeout_counter: uint;
        var continue_work: bool;
        continue_work = TRUE; 
        all of {
            {
                // this branch covers the case when the lower layer item 
                // is ready because of upper layer item (either because the 
                // size limit is reached or the upper layer signals that the
                // item is ready)

                while continue_work { // can be turned off from outside
                    var layering_struct: ex_mtm_layering_ml_pkt_s;
                    driver.remaining_bytes = 
                        ll_pkt_length - driver.tmp_payload.size();
                    layering_struct = ml_driver.get_next_item();

                    // payload 0 means that the upper layer signals that the 
                    // item can be sent to the BFM.
                    if layering_struct.payload.size() == 0 then {
                        driver.tmp_payload.resize(ll_pkt_length,TRUE,0,TRUE);
                        do ll_pkt keeping {
                            .payload == driver.tmp_payload;
                        };
                        driver.tmp_payload.clear();
                        timeout_counter = 0;
                    } else {
                        // the new upper layer object is added to the 
                        // lower layer data
                        driver.tmp_payload.add(layering_struct.payload);

                        // if the size limit is reached, the item is sent 
                        // to the BFM
                        if driver.tmp_payload.size() == ll_pkt_length {
                            do ll_pkt keeping {
                                .payload == driver.tmp_payload;
                            };
                            driver.tmp_payload.clear();                            
                            timeout_counter = 0;                       
                        };
                    };
                    emit ml_driver.item_done;
                };
                {
                    // this branch covers the case when the timeout counter 
                    // expires and an item must be supplied to the BFM.
                    while continue_work { // can be turned off from outside
                    
                        while timeout_counter < ll_pkt_length {
                            wait [1];
                            timeout_counter += 1;
                        };
                        driver.tmp_payload.resize(ll_pkt_length,TRUE,0,TRUE);
                        do ll_pkt keeping {
                            .payload == driver.tmp_payload;
                        };    
                        driver.tmp_payload.clear();
                        timeout_counter = 0;
                    };
                };
            };
        };
    };
};

'>



