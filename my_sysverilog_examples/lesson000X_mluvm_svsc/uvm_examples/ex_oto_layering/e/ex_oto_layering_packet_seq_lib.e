/*----------------------------------------------------------    
File name   : ex_oto_layering_packet_seq_lib.e
Title       : packet sequence library 
Project     : one to one layering example
Created     : 2007
Description : Defines reusable packet sequences for usage in tests
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

extend ex_oto_layering_packet_sequence_kind: [LAYERED];

extend LAYERED ex_oto_layering_packet_sequence {
    upper_layer_id: uint;
    is_relevant(): bool is only {
        result = (upper_layer_id == driver.stream_id);
    };
    
    body() @driver.clock is {
        do packet;
    };
};

'>

<'

// same as LAYERED sequence but calls LONG_P packets

extend ex_oto_layering_packet_sequence_kind: [LAYERED_LONG];

extend LAYERED_LONG ex_oto_layering_packet_sequence {
    upper_layer_id: uint;
    is_relevant(): bool is only {
        result = (upper_layer_id == driver.stream_id);
    };
    
    body() @driver.clock is {
        do LONG_P packet;
    };
};

'>


<'

// same as LAYERED sequence but calls SHORT_P packets

extend ex_oto_layering_packet_sequence_kind: [LAYERED_SHORT];

extend LAYERED_SHORT ex_oto_layering_packet_sequence {
    upper_layer_id: uint;
    is_relevant(): bool is only {
        result = (upper_layer_id == driver.stream_id);
    };
    
    body() @driver.clock is {
        do SHORT_P packet;
    };
};
        

'>
