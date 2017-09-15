/*----------------------------------------------------------    
File name   : ex_otm_layering_packet_seq_lib.e
Title       : packet sequence library 
Project     : one to many layering example
Created     : 2007
Description : Defines reusable atm sequences for usage in tests
Notes       : This is one of four layering examples: One to one, 
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 

<'

define ATM_TIMEOUT 2000;

extend ex_otm_layering_atm_sequence_kind: [LAYERED];

extend LAYERED ex_otm_layering_atm_sequence {
    
    atm_id: uint; // used for synchronizing with upper layer
    atm_header : uint (bits:40); 
    // atm cells are 5 bytes header and 48 bytes cell
    
    body() @driver.clock is only{

        var continue_work: bool;
        continue_work = TRUE; 
        
        while continue_work { // while there are more upper layer items
            first of {
                {
                    var layering_struct: layering_data_struct_s;
                    var num_of_cells: uint;
                    var size_of_cells: uint;
                    layering_struct = get_item_from_upper_layer(atm_id);
                    // gets upper layer item or stalls when there is none
                    
                    num_of_cells = 
                        (layering_struct.data.size() - 1)/ ATM_PAYLOAD_LEN + 1;
                    // fragmentation computation and implementation
                    size_of_cells = num_of_cells * ATM_PAYLOAD_LEN;
                    layering_struct.data.resize(size_of_cells,TRUE,0,TRUE);
                    for i from 0 to num_of_cells - 1 {
                        do cell keeping {
                            .payload == layering_struct.data[i * ATM_PAYLOAD_LEN..(i + 1) * ATM_PAYLOAD_LEN  - 1];
                            .header == atm_header;
                        };
                    };
                };
                {
                    // time out for upper layer items (can be increased or 
                    // decreased upon need) 
                    // enables stop_run from virtual sequence
                    wait [ATM_TIMEOUT];
                    continue_work = FALSE;
                };
            };
        };
    };
};

'>

<'
// this is an example for regular (non layered) atm sequence. 
// it can be called with no limitations during layered tests.

extend ex_otm_layering_atm_sequence_kind: [ALL_RED];
extend ALL_RED ex_otm_layering_atm_sequence {

    count: int[1..10];
    
    body() @driver.clock is {
        for i from 1 to count {
            do cell keeping {.color == RED};
        };
    };
};

'>


