/*----------------------------------------------------------    
File name   : ex_mtm_layering_ul_pkt_seq_lib.e
Title       : upper layer packet sequence library 
Project     : many to many layering example
Created     : 2007
Description : Defines reusable upper layer packet sequences for usage in tests
Notes       : This is one of four layering examples: One to one, 
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 
 
<'
extend ex_mtm_layering_ul_pkt_sequence {
    upper_layer_id: uint;
    
    is_relevant(): bool is only {
        result = (upper_layer_id == driver.stream_id);
    };
};

'>
    
<'
// this is an example for upper layer sequence. it does items only for the 
// lower layer sequence with the same stream id. it creates a scenario of upper 
// layer packet that ends on the border of two lower layer packets.

extend ex_mtm_layering_ul_pkt_sequence_kind: [EXACT];

extend EXACT ex_mtm_layering_ul_pkt_sequence {
    
    is_relevant(): bool is only {
        result = (upper_layer_id == driver.stream_id);
    };

    body() @driver.clock is {
        do ul_pkt keeping {
            driver.remaining_bytes <= 1518 =>  .len == driver.remaining_bytes;
        };
    };
};

'>

<'

// calls any ul_pkts

extend ex_mtm_layering_ul_pkt_sequence_kind: [LAYERED];

extend LAYERED ex_mtm_layering_ul_pkt_sequence {
    is_relevant(): bool is only {
        result = (upper_layer_id == driver.stream_id);
    };
    
    body() @driver.clock is {
        do ul_pkt;
    };
};

'>
<'

// calls any ul_headers in an infinite loop (imitates header) 

extend ex_mtm_layering_ul_header_sequence {
    upper_layer_id: uint;
    
    is_relevant(): bool is only {
        result = (upper_layer_id == driver.stream_id);
    };
};


extend ex_mtm_layering_ul_header_sequence_kind: [HEADER];

extend HEADER ex_mtm_layering_ul_header_sequence {
    
    is_relevant(): bool is only {
        result = (upper_layer_id == driver.stream_id);
    };
    
    body() @driver.clock is {
        while TRUE {
            do ul_header;
        };
    };
};

'>


