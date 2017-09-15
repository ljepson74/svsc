/*----------------------------------------------------------    
File name   : ex_mto_layering_ll_pkt_env.e
Title       : Defines the lower layer pkt env 
Project     : many to one layering example
Created     : 2007
Description : Defines the ll pkt env , agent and its sequence, item and 
            : driver. Also contains the interface for the upper layer. 
            : Defines the BFM.
Notes       : This is one of four layering examples: One to one, 
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 
 
    
o The ll pkt struct:

<'
type ex_mto_layering_ll_pkt_color: [RED, GREEN, BLUE];
define LL_MIN_PKT_LEN 64;
define LL_MAX_PKT_LEN 1518;

struct ex_mto_layering_ll_pkt_s like any_sequence_item {
    color: 	ex_mto_layering_ll_pkt_color;
    payload: 	list of byte;
    keep soft payload.size() in [LL_MIN_PKT_LEN..LL_MAX_PKT_LEN];
    
    -- How to print it in the "trace sequence"/"show sequence" output
    nice_string(): string is also {
        return append(result, " (", color,")");
    };
};

'>

o The BFM:

<'


unit ex_mto_layering_ll_pkt_bfm_u like uvm_bfm {
    
    // public interface
    d_enable: out simple_port of bit is instance; // ports to the DUT
    d_bus: out simple_port of byte is instance;   // ports to the DUT
    
    event a_clock is cycle @sys.any;  	-- The LL_PKT main clock
    event ll_pkt_started;			-- start of transfer to DUT
    event ll_pkt_ended;			-- end of transfer to DUT

    driver:ex_mto_layering_ll_pkt_driver_u;
    
    on a_clock {
        emit driver.clock;
    };
    
    
    -- A method which sends the ll_pkt into the DUT
    transfer_ll_pkt_to_dut(ll_pkt: ex_mto_layering_ll_pkt_s) @a_clock is {
        emit ll_pkt_started;
        message(MEDIUM,"Start sending ll_pkt data");
        d_enable$ = 1;
        for each (d) in ll_pkt.payload do {
            messagef(HIGH,"ll_pkt data: %s has been sent to the bus\n",d);
            d_bus$ = d;
            wait cycle;
        };
        d_enable$ = 0;
        wait cycle;
        emit ll_pkt_ended;
        messagef(MEDIUM, "Finished sending ll_pkt data\n");
        
    };
    
    pull_send_loop() @a_clock is {
        while TRUE {
            var ll_pkt := driver.get_next_item();
            transfer_ll_pkt_to_dut(ll_pkt);
            emit driver.item_done;
        };
    };
    
    run() is also {
        start pull_send_loop();
    };
    
    
};
'>


o Defining ll_pkt_sequence and hooking it up:

<'

-- Define ll_pkt_sequence, ll_pkt_sequence_kind and ll_pkt_driver
sequence ex_mto_layering_ll_pkt_sequence using item=ex_mto_layering_ll_pkt_s, 
    created_driver=ex_mto_layering_ll_pkt_driver_u;

#ifdef SPECMAN_VERSION_8_2_OR_LATER {
    // Before Specman 8.2, get item from upper layer is a blocking function

    -- Extend the base type with essential fields
    extend ex_mto_layering_ll_pkt_sequence {
        !ll_pkt: ex_mto_layering_ll_pkt_s;
        
        get_item_from_upper_layer(stream_id : uint,remaining_bytes: uint): 
            layering_data_struct_s @driver.clock is {  
            
            // This method returns item or NULL to the lower layer 
            result = driver.get_item_layer_transfer$(stream_id,
                remaining_bytes);
            if result != NULL then {
                message(MEDIUM,
                    "LL sequence got an item from the upper layer");
            };
        };
    };
} 
#else {

    -- Extend the base type with essential fields
    extend ex_mto_layering_ll_pkt_sequence {
        !ll_pkt: ex_mto_layering_ll_pkt_s;
        
        get_item_from_upper_layer(stream_id : uint,remaining_bytes: uint): 
            layering_data_struct_s @driver.clock is {  
            
            // This method blocks the lower layer while enabling other instances 
            // to call the upper layer
            while result == NULL {
                result = driver.get_item_layer_transfer$(stream_id,
                    remaining_bytes);
                if result == NULL then {
                    wait [1];
                } else {
                    message(MEDIUM,
                        "LL sequence got an item from the upper layer");
                };
            };
        };
    };
};


-- An interface method to upper layer 

extend ex_mto_layering_ll_pkt_driver_u {
    // method port to upper layer
    get_item_layer_transfer: 
        out method_port of item_layer_transfer is instance;
};




'>

o The enclosing LL_PKT agent:

<'

unit ex_mto_layering_ll_pkt_agent_u like uvm_agent {
    
    bfm: ex_mto_layering_ll_pkt_bfm_u is instance;
    -- One can also instantiate here an LL_PKT monitor unit, etc..
    driver: ex_mto_layering_ll_pkt_driver_u is instance;
    keep bfm.driver == driver;
};

'>

o The enclosing LL_PKT environment:

<'

unit ex_mto_layering_ll_pkt_env_u like uvm_env {
    
    logger    : message_logger is instance;
    file_logger      : message_logger  is instance;
    
    keep soft file_logger.to_screen == FALSE;
    keep soft file_logger.to_file == "ll_pkt";
    -- Instantiate a driver in the LL_PKT env
    
    evc_name : string;
    keep soft evc_name == "LL_PKT ";
    
    short_name(): string is only {
        return append(evc_name);
    };
    
    ll_pkt_color : vt_style;
    keep ll_pkt_color  == DARK_PURPLE;
    
    short_name_style(): vt_style is only {return ll_pkt_color;};

    agent: ex_mto_layering_ll_pkt_agent_u is instance;
};

'>


