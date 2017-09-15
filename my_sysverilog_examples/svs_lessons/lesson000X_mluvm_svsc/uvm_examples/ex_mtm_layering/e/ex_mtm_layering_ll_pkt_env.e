
/*----------------------------------------------------------    
File name   : ex_mtm_layering_ll_pkt_env.e
Title       : Defines the lower and mediating layer pkt env 
Project     : many to many layering example
Created     : 2007
Description : Defines the ll pkt env, agent and its sequence, item and Driver. 
            : in the same env it also defines the ml pkt its sequence and the 
            : interface for the upper layer. Defines the BFM.
Notes       : This is one of four layering examples: One to one, 
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 

    
o The ml pkt struct:
the ml pkt is a mediating layer struct. it gets payload from various upper 
layer agents. these layers might supply it with lower layer constructs 
(such as ll header) or upper layer constructs (such as upper layer packets)

<'

struct ex_mtm_layering_ml_pkt_s like any_sequence_item {
    payload: 	list of byte;
};

'>

o The ll pkt struct:
this is the combination of headers and upper layer packets that eventually get 
sent to the BFM. 
<'

struct ex_mtm_layering_ll_pkt_s like any_sequence_item {
    payload: 	list of byte;
    
    // How to print it in the "trace sequence"/"show sequence" output
    nice_string(): string is also {
        return append(result);
    };
};

'>

o The BFM:

<'


unit ex_mtm_layering_ll_pkt_bfm_u like uvm_bfm {
    
    // public interface
    d_enable: out simple_port of bit is instance; // ports to the DUT
    d_bus: out simple_port of byte is instance;   // ports to the DUT
    
    event a_clock is cycle @sys.any;  	-- The LL_PKT main clock
    event ll_pkt_started;		-- start of transfer to DUT
    event ll_pkt_ended;			-- end of transfer to DUT

    driver: ex_mtm_layering_ll_pkt_driver_u;
    
    on a_clock {
        emit driver.clock;
    };
    
    
    -- A method which sends the ll pkt into the DUT
    transfer_ll_pkt_to_dut(ll_pkt: ex_mtm_layering_ll_pkt_s) @a_clock is {
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
        messagef(MEDIUM,"Finished sending ll_pkt data\n");
        
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


o Defining ml_pkt_sequence and hooking it up:

<'

-- Define ml_pkt_sequence, ml_pkt_sequence_kind and ml_pkt_driver
sequence ex_mtm_layering_ml_pkt_sequence using item=ex_mtm_layering_ml_pkt_s, 
    created_driver=ex_mtm_layering_ml_pkt_driver_u;

-- Extend the base type with essential fields
extend ex_mtm_layering_ml_pkt_sequence {
    !ml_pkt: ex_mtm_layering_ml_pkt_s;

    // method port for upper layer. enables connection to any apper layer that
    // supports the method port format
    !get_item_layer_transfer: 
        out method_port of item_layer_transfer;

    // this method waits until an item is received from the method port. 
    // supports non blocking implementation in the upper layer
    get_item_from_upper_layer(stream_id : uint,remaining_bytes: uint): 
        layering_data_struct_s @driver.clock is {  
        
        while result == NULL {
            result = get_item_layer_transfer$(stream_id,remaining_bytes);
            if result == NULL then {
                wait [1];
            } else {
                message(MEDIUM,
                        "ML sequence got an item from the upper layer");
            };
        };
    };  
};

'>

o Defining ll_pkt_sequence and hooking it up:

<'

// Define ll_pkt_sequence, ll_pkt_sequence_kind and ll_pkt_driver
sequence ex_mtm_layering_ll_pkt_sequence using item=ex_mtm_layering_ll_pkt_s, 
    created_driver=ex_mtm_layering_ll_pkt_driver_u;

// Extend the base type with essential fields
extend ex_mtm_layering_ll_pkt_sequence {
    !ll_pkt: ex_mtm_layering_ll_pkt_s;
};

extend ex_mtm_layering_ll_pkt_driver_u {
    // these two parameters use as an inter sequence status holders.
    // both the ll seq and ml seq has visibility to them, and so, the ml seq 
    // can supply the right amount of data to the ll seq

    !remaining_bytes: uint;
    !tmp_payload: list of byte;
};

// An interface method to upper layer 
// the ml driver gets as many method ports as the different kinds of upper 
// layer agents, also it contains a pointer to ll driver to be able to watch 
// its status.
 
extend ex_mtm_layering_ml_pkt_driver_u {
    get_item_layer_transfers: list of  
        out method_port of item_layer_transfer is instance;

    ll_driver: ex_mtm_layering_ll_pkt_driver_u;
};




'>

o The enclosing LL_PKT agent:

<'

unit ex_mtm_layering_ll_pkt_agent_u like uvm_agent {
    
    bfm: ex_mtm_layering_ll_pkt_bfm_u is instance;
    -- One can also instantiate here an LL_PKT monitor unit, etc..
    ll_driver: ex_mtm_layering_ll_pkt_driver_u is instance;
    keep bfm.driver == ll_driver;
    ml_driver: ex_mtm_layering_ml_pkt_driver_u is instance;

    keep ml_driver.ll_driver == ll_driver;
    event ml_clock is cycle @sys.any;  	-- The LL_PKT main clock
    on ml_clock {
        emit ml_driver.clock;
    };
};

'>

o The enclosing LL_PKT environment:

<'

unit ex_mtm_layering_ll_pkt_env_u like uvm_env {
    
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
    
    agent: ex_mtm_layering_ll_pkt_agent_u is instance;    
    
};

'>


