/*----------------------------------------------------------    
File name   : ex_otm_layering_atm_env.e
Title       : Defines the lower layer (atm) env 
Project     : one to many layering example
Created     : 2007
Description : Defines the atm env, agent and its sequence, item and Driver 
            : which also contains the interface for the upper layer. 
            : Defines the BFM.
Notes       : This is one of four layering examples: One to one, 
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 
    
o The cell:

<'
define ATM_PAYLOAD_LEN 48;
define ATM_HEADER_LEN 5;
define ATM_HEADER_LEN_BITS 40;

type ex_otm_layering_atm_color: [RED, GREEN, BLUE];
type ex_otm_layering_atm_cell_kind: [A1, A2, A3, A4];

struct ex_otm_layering_atm_cell like any_sequence_item {
    kind: 	ex_otm_layering_atm_cell_kind;
    color: 	ex_otm_layering_atm_color;
    header: 	uint(bits:ATM_HEADER_LEN_BITS);
    !header_list[ATM_HEADER_LEN]: list of byte; 
    payload[ATM_PAYLOAD_LEN]: 	list of byte;
    
    -- How to print it in the "trace sequence"/"show sequence" output
    nice_string(): string is also {
        return append(result, " (", kind, " ", color,")");
    };
    
    is_relevant(): bool is {
        // If change of back pressure value happened during generation 
        // and the current item can not be sent to the DUT, it is held
        // until the back_pressure ceases. Other items (from other sequences)
        // are not blocked
        result = driver.back_pressure_value != header;
        if not result then {
            message(MEDIUM, "backpressure is on. item not relevant");
        };
    };  
};

'>

o The BFM:

<'


unit ex_otm_layering_atm_bfm_u like uvm_bfm {
    
    // public interface
    !driver  : ex_otm_layering_atm_driver_u;
    d_enable : out simple_port of bit is instance;      // ports to the DUT
    d_bus    : out simple_port of byte is instance;     // ports to the DUT
    back_pressure: in simple_port of byte is instance; // ports from the DUT

    event a_clock is cycle @sys.any;  	// The ATM main clock
    event cell_started;			// start of transfer to DUT
    event cell_ended;			// end of transfer to DUT
    
    on a_clock {
        emit driver.clock;
    };
    
    
    -- A method which sends the cell into the DUT
    transfer_cell_to_dut(cell: ex_otm_layering_atm_cell) @a_clock is {
        emit cell_started;
        message(MEDIUM, "BFM starts sending atm data");
        d_enable$ = 1;
        cell.header_list = pack(NULL,cell.header);
        for each (d) in cell.header_list do {
            messagef(HIGH, "atm data: %s has been sent to the bus\n",d);
            d_bus$ = d;
            wait cycle;
        };
        for each (d) in cell.payload do {
            messagef(HIGH, "atm data: %s has been sent to the bus\n",d);
            d_bus$ = d;
            wait cycle;
        };
        d_enable$ = 0;
        wait cycle;
        emit cell_ended;
        messagef(MEDIUM, "BFM finished sending atm data\n");
        
    };
    
    // Back preassure value might change while next item is generated. 
    detect_back_preassure() @a_clock is {
        while TRUE {
            driver.back_pressure_value = back_pressure$;
            wait[1];
        };
    };
    
    pull_send_loop() @a_clock is {
        start detect_back_preassure();
        while TRUE {
            var cell := driver.get_next_item();
            transfer_cell_to_dut(cell);
            emit driver.item_done;
        };
    };
    
    run() is also {
        start pull_send_loop();
    };
    
    
};
'>


o Defining atm_sequence and hooking it up:

<'

-- Define atm_sequence, atm_sequence_kind and atm_driver
sequence ex_otm_layering_atm_sequence using item=ex_otm_layering_atm_cell, created_driver=ex_otm_layering_atm_driver_u;

-- Extend the base type with essential fields
extend ex_otm_layering_atm_sequence {
    !cell: ex_otm_layering_atm_cell;
    get_item_from_upper_layer(stream_id : uint): 
                                 layering_data_struct_s @driver.clock is {  
        while result == NULL {
            result = driver.get_item_layer_transfer$(stream_id);
            if result == NULL then {
                wait [1];
            } else {
                message(MEDIUM,
                        "ATM sequence got an item from the upper layer");
            };
        };
    };
};


-- An interface method to upper layer 

extend ex_otm_layering_atm_driver_u {
    get_item_layer_transfer: out method_port of item_layer_transfer
                                                          is instance;
    !back_pressure_value: uint(bits:40);

};




'>

o The enclosing ATM agent:

<'

unit ex_otm_layering_atm_agent_u like uvm_agent {
    
    bfm    : ex_otm_layering_atm_bfm_u is instance;
    -- One can also instantiate here an ATM monitor unit, etc..
    driver : ex_otm_layering_atm_driver_u is instance;
    
    connect_pointers() is also {
        bfm.driver = driver;
    };
};

'>
o The enclosing ATM environment:

<'

unit ex_otm_layering_atm_env_u like uvm_env {
    
    logger        : message_logger is instance;
    file_logger   : message_logger  is instance;
    
    keep soft file_logger.to_screen == FALSE;
    keep soft file_logger.to_file == "atm";
    -- Instantiate a driver in the ATM env
    
    evc_name : string;
    keep soft evc_name == "ATM ";
    
    short_name(): string is only {
        return append(evc_name);
    };
    
    atm_color : vt_style;
    keep atm_color  == DARK_PURPLE;
    
    short_name_style(): vt_style is only {return atm_color;};
    
    agent: ex_otm_layering_atm_agent_u is instance;
};

'>
