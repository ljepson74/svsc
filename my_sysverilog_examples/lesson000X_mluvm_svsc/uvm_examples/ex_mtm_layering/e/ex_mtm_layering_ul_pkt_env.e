/*----------------------------------------------------------    
File name   : ex_mtm_layering_ul_pkt_env.e
Title       : Defines the upper layer packet env 
Project     : many to many layering example
Created     : 2007
Description : Defines the upper layer packet env, agent and its sequence, 
            : item and driver. Defines the BFM and the interface method to 
            : lower layer.
Notes       : This is one of four layering examples: One to one, 
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 
 
    
o The Packet:

<'
define UL_PKT_ZERO_LEN 0;
define UL_PKT_MIN_LEN 64;
define UL_PKT_THRSH_LEN 96;
define UL_PKT_MAX_LEN 512;

// The packet struct is an abstract data type designed to 
// demonstrate layering. It is not a part of any known protocol

type ex_mtm_layering_ul_pkt_length_t: [SHORT_P, LONG_P,ZERO_P];

struct ex_mtm_layering_ul_pkt like any_sequence_item {

    length_range: ex_mtm_layering_ul_pkt_length_t;
    len: uint;
    keep length_range == ZERO_P => soft len == UL_PKT_ZERO_LEN;
    keep length_range == SHORT_P =>
                soft len in [UL_PKT_MIN_LEN..UL_PKT_THRSH_LEN];
    keep length_range == LONG_P =>
            soft len in [UL_PKT_THRSH_LEN + 1..UL_PKT_MAX_LEN];
    
    %payload[len]: list of byte;
    keep soft length_range != ZERO_P;

    nice_string(): string is also {
        result = append(result, " (", length_range, " ", len, ")");
    };
};

'>


o The ul_pkt BFM:

<'

unit ex_mtm_layering_ul_pkt_bfm_u like uvm_bfm {
    
    // public interface
    
    p_driver: ex_mtm_layering_ul_pkt_driver_u;
    
    event p_clock is cycle @sys.any;  	-- The ATM main clock
    
    on p_clock {
        emit p_driver.clock;
    };
    // private interface
    driver_locker: locker;
    -- An interface method to lower layer 
    
    down_item_layer_transfer: 
        in method_port of item_layer_transfer is instance;

    // This method tries to get an item from the driver. 
    // It calls try_next_item and not get_next_item so the driver is 
    // not blocked by any lower layer request
    
    down_item_layer_transfer(stream_id: uint,remaining_bytes: uint): 
        layering_data_struct_s @sys.any is {
        
        driver_locker.lock();
        var ul_pkt_item: ex_mtm_layering_ul_pkt;
        p_driver.stream_id = stream_id;
        p_driver.remaining_bytes = remaining_bytes;
        ul_pkt_item = p_driver.try_next_item();
        if ul_pkt_item != NULL {
            result = new;
            result.data = pack(NULL, ul_pkt_item);
            result.upper_layer_struct = ul_pkt_item;
            message(MEDIUM, "UL BFM gives an item to the lower layer");
            emit p_driver.item_done; 
        } else {
            result = NULL;
        };
        driver_locker.unlock();
    };
};

'>

o Defining ul_pkt_sequence and hooking it up:

<'
-- Define ul_pkt_sequence, ul_pkt_sequence_kind and ul_pkt_driver
sequence ex_mtm_layering_ul_pkt_sequence using item=ex_mtm_layering_ul_pkt, 
    created_driver=ex_mtm_layering_ul_pkt_driver_u;

extend ex_mtm_layering_ul_pkt_driver_u {
    !stream_id : uint;
    !remaining_bytes: uint;
};

-- Extend the base type with essential fields
extend ex_mtm_layering_ul_pkt_sequence {
    !ul_pkt: ex_mtm_layering_ul_pkt;
};

'>

o The enclosing UL_PKT agent:

<'

unit ex_mtm_layering_ul_pkt_agent_u like uvm_agent {

    driver: ex_mtm_layering_ul_pkt_driver_u is instance;
    
    bfm: ex_mtm_layering_ul_pkt_bfm_u is instance;
    keep bfm.p_driver == driver;
};

'>

o The enclosing UL_PKT environment:

<'

unit ex_mtm_layering_ul_pkt_env_u like uvm_env {
    -- One can also instantiate here an ul_pkt monitor unit, etc..
    logger    : message_logger is instance;
    file_logger      : message_logger  is instance;
    
    keep soft file_logger.to_screen == FALSE;
    keep soft file_logger.to_file == "ul_pkt";
    
    agent: ex_mtm_layering_ul_pkt_agent_u is instance;
    
};

'>


