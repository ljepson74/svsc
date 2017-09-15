
/*----------------------------------------------------------    
File name   : ex_mtm_layering_ml_pkt_seq_lib_using_pre_do.e
Title       : packet sequence library 
Project     : many to one layering example
Created     : 2007
Description : Defines reusable ml pkt sequences for usage in tests. two 
            : sequences are defined, one for header and one for upper layer 
            : packets. each sequence interfaces through a designated method 
            : port with its upper layer.the upper layer sequences sync through 
            : is_relevant methods with each other.
Notes       : This file implements the ml pkt using the older sequences 
            : mechanism, which did not have deliver_item.
            : So building the item is implemented in the pre_do()
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 

  

<'
type ml_seq_role_t: [HEADER,PAYLOAD];
extend ex_mtm_layering_ml_pkt_sequence_kind: [LAYERED];

extend LAYERED ex_mtm_layering_ml_pkt_sequence {
    
    ml_pkt_id: uint; // used for synchronizing with upper layer
    !do_payload: list of byte;
    !tmp_payload : list of byte;
    ml_seq_role : ml_seq_role_t;
    
    pre_do(is_item: bool) @sys.any is {
        if is_item {
            if driver.ll_driver.remaining_bytes > 0 then {
                if driver.ll_driver.remaining_bytes >= tmp_payload.size() {
                    do_payload = tmp_payload.copy();
                    tmp_payload.clear();
                } else {
                    do_payload = tmp_payload[0..driver.ll_driver.remaining_bytes - 1];
                    tmp_payload = tmp_payload[driver.ll_driver.remaining_bytes..];
                };
            } else {
                do_payload.clear();
            };  
        };
    };
    
    body() @driver.clock is only{
        var continue_work: bool;
        continue_work = TRUE; 
        while continue_work { // while there are more upper layer items
            var layering_struct: layering_data_struct_s;
            layering_struct = get_item_from_upper_layer(ml_pkt_id, 
                driver.ll_driver.remaining_bytes);
 
            // gets upper layer item or stalls when there is none
            tmp_payload = layering_struct.data.copy();
            
            while tmp_payload is not empty {
                do ml_pkt keeping {
                    .payload == do_payload;
                };
            };
        };
    };
};

'>

<'
extend HEADER LAYERED ex_mtm_layering_ml_pkt_sequence {
    
    is_relevant(): bool is {
        result = driver.ll_driver.tmp_payload is empty;
    };
};
'>

<'
extend PAYLOAD LAYERED ex_mtm_layering_ml_pkt_sequence {
    
    is_relevant(): bool is {
        result = driver.ll_driver.tmp_payload is not empty;
    };
};
'>



