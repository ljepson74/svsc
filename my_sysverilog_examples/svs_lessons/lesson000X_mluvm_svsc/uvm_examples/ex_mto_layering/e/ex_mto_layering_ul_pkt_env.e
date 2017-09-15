/*----------------------------------------------------------    
File name   : ex_mto_layering_ul_pkt_env.e
Title       : Defines the upper layer packet env 
Project     : many to one layering example
Created     : 2007
Description : Defines the upper layer packet env and its sequence, 
            : item and driver. Defines the BFM and the interface method 
            : to lower layer.
Notes       : This is one of four layering examples: One to one, 
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 

o The Packet:

<'
define UL_ZERO_SIZE 0;
define UL_MIN_SIZE 64;
define UL_THRSH_SIZE 96;
define UL_MAX_SIZE 512;

// The packet struct is an abstract data type designed to 
// demonstrate layering. It is not a part of any known protocol

type ex_mto_layering_ul_pkt_length_t: [SHORT_P, LONG_P,ZERO_P];

struct ex_mto_layering_ul_pkt like any_sequence_item {
    length_range: ex_mto_layering_ul_pkt_length_t;
    len: uint;
    keep length_range == ZERO_P => soft len == UL_ZERO_SIZE;
    keep length_range == SHORT_P => soft len in [UL_MIN_SIZE..UL_THRSH_SIZE];
    keep length_range == LONG_P => soft len in [UL_THRSH_SIZE+1..UL_MAX_SIZE];
    %payload[len]: list of byte;
    
    nice_string(): string is also {
        result = append(result, " (", length_range, " ", len, ")");
    };
};

'>


o The ul_pkt BFM:

<'

unit ex_mto_layering_ul_pkt_bfm_u like uvm_bfm {
    
    // public interface
    
    p_driver: ex_mto_layering_ul_pkt_driver_u;
    
    event p_clock is cycle @sys.any;  	-- The ATM main clock
    
    on p_clock {
        emit p_driver.clock;
    };
    // private interface
    driver_locker: locker;
    -- An interface method to lower layer 
    
    down_item_layer_transfer: in method_port of item_layer_transfer
                                                            is instance;

    // This method try to get an item from the driver. 
    // It calls try_next_item and not get_next_item so the driver is 
    // not blocked by any lower layer request
    
    down_item_layer_transfer(stream_id: uint,
                             remaining_bytes: uint): 
                                 layering_data_struct_s @sys.any is {
        
       driver_locker.lock(); // only one request can be active in each cycle;
        var ul_pkt_item: ex_mto_layering_ul_pkt;
        p_driver.stream_id = stream_id;
        p_driver.remaining_bytes = remaining_bytes;
        ul_pkt_item = p_driver.try_next_item();
        if ul_pkt_item != NULL { // there was an item from the upper layer
            result = new;
            result.data = pack(NULL, ul_pkt_item);
            result.upper_layer_struct = ul_pkt_item;
            message(MEDIUM, "UL BFM gives an item to the lower layer");
            emit p_driver.item_done; 
        } else { // no item from upper layer
            result = NULL;
        };
        driver_locker.unlock();
    };
};

'>

o Defining ul_pkt_sequence and hooking it up:

<'
-- Define ul_pkt_sequence, ul_pkt_sequence_kind and ul_pkt_driver
sequence ex_mto_layering_ul_pkt_sequence using item=ex_mto_layering_ul_pkt, 
    created_driver=ex_mto_layering_ul_pkt_driver_u;

extend ex_mto_layering_ul_pkt_driver_u {
    !stream_id : uint; // for sync of lower and upper sequences
    !remaining_bytes: uint; // info from lower to upper layer
};

-- Extend the base type with essential fields
extend ex_mto_layering_ul_pkt_sequence {
    !ul_pkt: ex_mto_layering_ul_pkt;
};

'>

o The enclosing UL_PKT agent:

<'

unit ex_mto_layering_ul_pkt_agent_u like uvm_agent {
    
    driver: ex_mto_layering_ul_pkt_driver_u is instance;
    
    bfm: ex_mto_layering_ul_pkt_bfm_u is instance;
    keep bfm.p_driver == driver;
};

'>

o The enclosing UL_PKT environment:

<'

unit ex_mto_layering_ul_pkt_env_u like uvm_env {
    -- One can also instantiate here an ul_pkt monitor unit, etc..
    logger    : message_logger is instance;
    file_logger      : message_logger  is instance;
    
    keep soft file_logger.to_screen == FALSE;
    keep soft file_logger.to_file == "ul_pkt";
    
    agent: ex_mto_layering_ul_pkt_agent_u is instance;    
};

'>


