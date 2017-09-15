/*----------------------------------------------------------    
File name   : ex_oto_layering_ul_packet_env.e
Title       : Defines the upper layer env 
Project     : one to one layering example
Created     : 2007
Description : Defines the packet env, agent and its sequence, item and 
            : Driver. 
            : In the agent, defines the BFM and the interface method to 
            : lower layer.
            : The main parts in this file are the BFM and its ports 
            : and methods
            :   in method_port down_item_layer_transfer
            :   in method_port ul_check_do_available 
Notes       : This is one of four layering examples: One to one,
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 

    
o The Packet:

<'
// The packet struct is an abstract data type designed to 
// demonstrate layering. It is not a part of any known protocol
define PACKET_MIN_LEN 64;
define PACKET_THRSH_LEN 96;
define PACKET_MAX_LEN 1518;

type ex_oto_layering_packet_kind_t: [KIND_A, KIND_B];
type ex_oto_layering_packet_length_t: [SHORT_P, LONG_P];

struct ex_oto_layering_packet like any_sequence_item {
    kind : ex_oto_layering_packet_kind_t;
    length_range: ex_oto_layering_packet_length_t;
    len: uint;
    keep length_range == SHORT_P => soft len in 
        [PACKET_MIN_LEN..PACKET_THRSH_LEN];
    keep length_range == LONG_P => soft len in 
        [PACKET_THRSH_LEN + 1 ..PACKET_MAX_LEN];
    %payload[len]: list of byte;
    
    nice_string(): string is also {
        result = append(result, " (",kind, " ", length_range, " ", len, ")");
    };
};

'>


o The packet BFM:

<'

unit ex_oto_layering_packet_bfm_u like uvm_bfm {
    
    // public interface
    
    p_driver: ex_oto_layering_packet_driver_u;
    
    event p_clock is cycle @sys.any;  	-- The ATM main clock
    
    on p_clock {
        emit p_driver.clock;
    };
    
    -- An interface method to lower layer 
    
    down_item_layer_transfer: in method_port of item_layer_transfer
                                                            is instance;
    // This method tries to get an item from the driver. 
    // It calls try_next_item and not get_next_item, so the driver
    // is not blocked by any lower layer request
    
    down_item_layer_transfer(stream_id: uint):
                     layering_data_struct_s @sys.any is {
        
        var packet_item: ex_oto_layering_packet;
        p_driver.stream_id = stream_id;
        packet_item = p_driver.try_next_item();
        if packet_item != NULL {
            result = new;
            result.data = pack(NULL, packet_item);
            result.upper_layer_struct = packet_item;
            message(MEDIUM, "Packet BFM gives an item to the lower layer");
            emit p_driver.item_done; 
        } else {
            result = NULL;
        };
    };

    ul_check_do_available: in method_port of check_do_available is instance;
    ul_check_do_available(stream_id: uint): bool is {
        p_driver.stream_id = stream_id;
        result = p_driver.has_do_available();
    };
};

'>

o Defining packet_sequence and hooking it up:

<'
-- Define packet_sequence, packet_sequence_kind and packet_driver
sequence ex_oto_layering_packet_sequence using item=ex_oto_layering_packet, 
    created_driver=ex_oto_layering_packet_driver_u;

extend ex_oto_layering_packet_driver_u {
    !stream_id : uint;
};

-- Extend the base type with essential fields
extend ex_oto_layering_packet_sequence {
    !packet: ex_oto_layering_packet;
};

'>

o The enclosing PACKET agent:

<'

unit ex_oto_layering_packet_agent_u like uvm_agent {

    driver: ex_oto_layering_packet_driver_u is instance;
    
    bfm: ex_oto_layering_packet_bfm_u is instance;
    
    keep bfm.p_driver == driver;
};

'>

o The enclosing PACKET environment:

<'

unit ex_oto_layering_packet_env_u like any_env {
    -- One can also instantiate here an packet monitor unit, etc..
    logger    : message_logger is instance;
    file_logger      : message_logger  is instance;
    
    keep soft file_logger.to_screen == FALSE;
    keep soft file_logger.to_file == "packet";
    
    agent: ex_oto_layering_packet_agent_u is instance;    
};

'>


