/*----------------------------------------------------------    
File name   : ex_mtm_layering_ul_header_env.e
Title       : Defines the upper layer header env 
Project     : many to many layering example
Created     : 2007
Description : Defines the upper layer header env, agent and its sequence, 
            : item and Driver. Defines the BFM and the interface method to 
            : lower layer.
Notes       : This is one of four layering examples: One to one, 
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 

    
o The header:

<'
define UL_HEADER_LEN 256;

// The header struct is an abstract data type designed to 
// demonstrate layering. It is not a part of any known protocol

struct ex_mtm_layering_ul_header like any_sequence_item {

    len: uint;
    keep soft len == UL_HEADER_LEN;
    %payload[len]: list of byte;

    nice_string(): string is also {
        result = append(result, " (", len, ")");
    };
};

'>


o The ul_header BFM:

<'

unit ex_mtm_layering_ul_header_bfm_u like uvm_bfm {
    
    // public interface
    
    h_driver: ex_mtm_layering_ul_header_driver_u;
    
    event h_clock is cycle @sys.any;  	-- The ATM main clock
    
    on h_clock {
        emit h_driver.clock;
    };
    // private interface
    driver_locker: locker;
    -- An interface method to lower layer 
    
    down_item_layer_transfer: 
        in method_port of item_layer_transfer is instance;

    // This method tries to get an item from the driver. 
    // It calls try_next_item and not get_next_item so the driver is 
    // not blocked by any lower layer request
    
    down_item_layer_transfer(stream_id: uint, remaining_bytes: uint): 
            layering_data_struct_s @sys.any is {
        
        driver_locker.lock();
        var ul_header_item: ex_mtm_layering_ul_header;
        h_driver.stream_id = stream_id;
        h_driver.remaining_bytes = remaining_bytes;
        ul_header_item = h_driver.try_next_item();
        if ul_header_item != NULL {
            result = new;
            result.data = pack(NULL, ul_header_item);
            result.upper_layer_struct = ul_header_item;
            message(MEDIUM, "UL BFM gives an item to the lower layer");
            emit h_driver.item_done; 
        } else {
            result = NULL;
        };
        driver_locker.unlock();
    };
};

'>

o Defining ul_header_sequence and hooking it up:

<'
-- Define ul_header_sequence, ul_header_sequence_kind and ul_header_driver
sequence ex_mtm_layering_ul_header_sequence using item=ex_mtm_layering_ul_header, 
    created_driver=ex_mtm_layering_ul_header_driver_u;

extend ex_mtm_layering_ul_header_driver_u {
    !stream_id : uint;
    !remaining_bytes: uint;
};

-- Extend the base type with essential fields
extend ex_mtm_layering_ul_header_sequence {
    !ul_header: ex_mtm_layering_ul_header;
};

'>

o The enclosing UL_HEADER agent:

<'

unit ex_mtm_layering_ul_header_agent_u like uvm_agent {

    driver: ex_mtm_layering_ul_header_driver_u is instance;
    
    bfm: ex_mtm_layering_ul_header_bfm_u is instance;
    keep bfm.h_driver == driver;
};

'>

o The enclosing UL_HEADER environment:

<'

unit ex_mtm_layering_ul_header_env_u like uvm_env {
    -- One can also instantiate here an ul_header monitor unit, etc..
    logger    : message_logger is instance;
    file_logger      : message_logger  is instance;
    
    keep soft file_logger.to_screen == FALSE;
    keep soft file_logger.to_file == "ul_header";
    
    agent: ex_mtm_layering_ul_header_agent_u is instance;
    
};

'>


