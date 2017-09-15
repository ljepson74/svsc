/*----------------------------------------------------------    
File name   : ex_oto_layering_ll_frame_env.e
Title       : Defines the lower layer env 
Project     : one to one layering example
Created     : 2007
Description : Defines the lower layer env, data-item (frame), bfm,  
            : driver, sequence.
            :
            : The main part in this file is the 
            : oto_ll_frame_driver_u and its methods:
            :   out method_port ll_check_do_available
            :   out method_port get_item_layer_transfer
            :   method get_item_from_upper_layer
            :      Gets item from upper layer, via the 
            :      get_item_layer_transfer port. 
            :
Notes       : This is one of four layering examples: One to one,
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 

o The frame:

<'
define ADDRESS_LEN_BITS 48;
define HEADER_LEN 12;
type ex_oto_layering_frame_color: [RED, GREEN, BLUE];

struct ex_oto_layering_frame_s like any_sequence_item {
    color: 	ex_oto_layering_frame_color;
    source_address: 	   uint(bits:ADDRESS_LEN_BITS);
    destination_address:   uint(bits:ADDRESS_LEN_BITS);
    !header_list[HEADER_LEN]: list of byte; 
    payload: 	list of byte;
    
    -- How to print it in the "trace sequence"/"show sequence" output
    nice_string(): string is also {
        return append(result, " (", color,")");
    };
};

'>

o The BFM:

<'


unit ex_oto_layering_frame_bfm_u like uvm_bfm {
    
    // public interface
    d_enable: out simple_port of bit is instance; // ports to the DUT
    d_bus: out simple_port of byte is instance;   // ports to the DUT
    
    event a_clock is cycle @sys.any;  	-- The FRAME main clock
    event frame_started;			-- start of transfer to DUT
    event frame_ended;			-- end of transfer to DUT

    driver:ex_oto_layering_frame_driver_u;
    
    on a_clock {
        emit driver.clock;
    };
    
    
    -- A method which sends the frame into the DUT
    transfer_frame_to_dut(frame: ex_oto_layering_frame_s) @a_clock is {
        emit frame_started;
        message(MEDIUM,"Start sending frame data");
        d_enable$ = 1;
        frame.header_list = pack(NULL,
            frame.destination_address,
            frame.source_address);
        for each (d) in frame.header_list do {
            messagef(HIGH,"frame data: %s has been sent to the bus\n",d);
            d_bus$ = d;
            wait cycle;
        };
        for each (d) in frame.payload do {
            messagef(HIGH,"frame data: %s has been sent to the bus\n",d);
            d_bus$ = d;
            wait cycle;
        };
        d_enable$ = 0;
        wait cycle;
        emit frame_ended;
        messagef(MEDIUM,"Finished sending frame data\n");
        
    };
    
    pull_send_loop() @a_clock is {
        while TRUE {
            var frame := driver.get_next_item();
            transfer_frame_to_dut(frame);
            emit driver.item_done;
        };
    };
    
    run() is also {
        start pull_send_loop();
    };
    
    
};
'>


o Defining frame_sequence and hooking it up:

<'

-- Define frame_sequence, frame_sequence_kind and frame_driver
sequence ex_oto_layering_frame_sequence using item=ex_oto_layering_frame_s, 
    created_driver=ex_oto_layering_frame_driver_u;

-- Extend the base type with essential fields
extend ex_oto_layering_frame_sequence {
    !frame: ex_oto_layering_frame_s;
};


-- An interface method to upper layer 

extend ex_oto_layering_frame_driver_u {
    ll_check_do_available   : out method_port of check_do_available
                                                              is instance; 
    get_item_layer_transfer : out method_port of item_layer_transfer
                                                              is instance;
    
    // get_item_from_upper_layer()
    //
    get_item_from_upper_layer(stream_id : uint):
                              layering_data_struct_s @clock is {  
        
        while result == NULL {
            result = get_item_layer_transfer$(stream_id);
            if result == NULL then {
                wait [1];
            } else {
                message(MEDIUM,
                        "Frame sequence got an item from the upper layer");
            };
        };
    };
};




'>

o The enclosing FRAME agent:

<'

unit ex_oto_layering_frame_agent_u like uvm_agent {
    
    bfm: ex_oto_layering_frame_bfm_u is instance;
    -- One can also instantiate here an FRAME monitor unit, etc..
    driver: ex_oto_layering_frame_driver_u is instance;
    keep bfm.driver == driver;
};

'>

o The enclosing FRAME environment:

<'

unit ex_oto_layering_frame_env_u like uvm_env {
    
    logger    : message_logger is instance;
    file_logger      : message_logger  is instance;
    
    keep soft file_logger.to_screen == FALSE;
    keep soft file_logger.to_file == "frame";
    -- Instantiate a driver in the FRAME env
    
    evc_name : string;
    keep soft evc_name == "FRAME ";
    
    short_name(): string is only {
        return append(evc_name);
    };
    
    frame_color : vt_style;
    keep frame_color  == DARK_PURPLE;
    
    short_name_style(): vt_style is only {return frame_color;};

    agent: ex_oto_layering_frame_agent_u is instance;    
};

'>
