/*----------------------------------------------------------    
File name   : ex_mto_layering_ul_pkt_seq_lib.e
Title       : upper layer packet sequence library 
Project     : many to one layering example
Created     : 2007
Description : Defines reusable upper layer packet sequences for usage 
            : in tests
Notes       : This is one of four layering examples: One to one, 
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 

    
<'
// this is an example for upper layer sequence. it does items only for the 
// lower layer sequence with the same stream id

extend ex_mto_layering_ul_pkt_sequence_kind: [LAYERED];

extend LAYERED ex_mto_layering_ul_pkt_sequence {
    upper_layer_id: uint;
    
    is_relevant(): bool is only {
        result = (upper_layer_id == driver.stream_id);
    };
    // it is very important that all length calculations are done in the time 
    // of item generation so no other working sequence can spoil the result.
    body() @driver.clock is {
        do ul_pkt keeping {
            driver.remaining_bytes < UL_MIN_SIZE => .length_range == ZERO_P;
            driver.remaining_bytes <= UL_THRSH_SIZE and driver.remaining_bytes >= UL_MIN_SIZE => 
                .length_range in [ZERO_P,SHORT_P];
            driver.remaining_bytes > UL_THRSH_SIZE => 
                .length_range in [ZERO_P,SHORT_P,LONG_P];
            .len <= driver.remaining_bytes            
        };
    };
};

'>

<'

// same as LAYERED sequence but calls LONG_P ul_pkts

extend ex_mto_layering_ul_pkt_sequence_kind: [LAYERED_LONG];

extend LAYERED_LONG ex_mto_layering_ul_pkt_sequence {
    upper_layer_id: uint;
    is_relevant(): bool is only {
        result = (upper_layer_id == driver.stream_id);
    };
    
    body() @driver.clock is {
        do ul_pkt keeping {
            driver.remaining_bytes <= UL_THRSH_SIZE => .length_range == ZERO_P;
            driver.remaining_bytes > UL_THRSH_SIZE => .length_range == LONG_P;
            .len <= driver.remaining_bytes            
        };  
    };
};

'>


<'

// same as LAYERED sequence but calls SHORT_P ul_pkts

extend ex_mto_layering_ul_pkt_sequence_kind: [LAYERED_SHORT];

extend LAYERED_SHORT ex_mto_layering_ul_pkt_sequence {
    upper_layer_id: uint;
    is_relevant(): bool is only {
        result = (upper_layer_id == driver.stream_id);
    };
    
    body() @driver.clock is {
        do ul_pkt keeping {
            driver.remaining_bytes < UL_MIN_SIZE => .length_range == ZERO_P;
            driver.remaining_bytes >= UL_MIN_SIZE => .length_range == SHORT_P;
            .len <= driver.remaining_bytes            
        };  
    };
};
        

'>
