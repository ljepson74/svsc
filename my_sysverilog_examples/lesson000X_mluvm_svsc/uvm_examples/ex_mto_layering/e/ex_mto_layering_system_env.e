/*----------------------------------------------------------    
File name   : ex_mto_layering_system_env.e
Title       : Defines the system env 
Project     : many to one layering example
Created     : 2007
Description : Defines the system env and its virtual Driver. 
            : Instansiates the two layers and binds them.
Notes       : This is one of four layering examples: One to one, 
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 

o disable MAIN BFM sequences:

<'


extend MAIN ex_mto_layering_ul_pkt_sequence {    
    keep soft count == 0;
};


extend MAIN ex_mto_layering_ll_pkt_sequence {
    keep soft count == 0;
};

'>

o The virtual sequence definition

<'
sequence system_sequence using created_driver = system_driver_u;

extend system_sequence {
    // pointers to BFM sequences
    !ul_pkt_sequence: ex_mto_layering_ul_pkt_sequence;
    !ll_pkt_sequence: ex_mto_layering_ll_pkt_sequence;
    
    // driver hookup
    keep ul_pkt_sequence.driver == driver.ul_pkt_driver;
    keep ll_pkt_sequence.driver == driver.ll_pkt_driver;
};


extend system_driver_u {
    // the drivers are instanciated in the sub environments and are 
    // only reused here 
    ul_pkt_driver : ex_mto_layering_ul_pkt_driver_u;
    ll_pkt_driver : ex_mto_layering_ll_pkt_driver_u;

    event clock is only @sys.any;

    get_sub_drivers(): list of any_sequence_driver is {
        return ({ul_pkt_driver; ll_pkt_driver});
    }; // get_sub_drivers...
};
'>

o System env definition

<'

unit system_env_u like uvm_env {

    ll_pkt_env : ex_mto_layering_ll_pkt_env_u is instance;
    ul_pkt_env : ex_mto_layering_ul_pkt_env_u is instance;
    
    system_driver: system_driver_u is instance;

    keep system_driver.ul_pkt_driver == ul_pkt_env.agent.driver;
    
    keep system_driver.ll_pkt_driver == ll_pkt_env.agent.driver;
    
    // binding the layeres together
    keep bind (ll_pkt_env.agent.driver.get_item_layer_transfer,
               ul_pkt_env.agent.bfm.down_item_layer_transfer);
    
    // binding the ll_pkt BFM to the DUT (empty in this example)
    keep bind (ll_pkt_env.agent.bfm.d_enable,empty);
    keep bind (ll_pkt_env.agent.bfm.d_bus,empty);
};

extend sys {
    system_env : system_env_u is instance;
};

'>
