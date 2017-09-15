/*----------------------------------------------------------    
File name   : ex_oto_layering_system_env.e
Title       : Defines the system env 
Project     : one to one layering example
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


extend MAIN ex_oto_layering_packet_sequence {    
    keep soft count == 0;
};


extend MAIN ex_oto_layering_frame_sequence {    
    keep soft count == 0;
};

'>

o The virtual sequence definition

<'
sequence system_sequence using created_driver = system_driver_u;

extend system_sequence {
    !packet_sequence: ex_oto_layering_packet_sequence;
    !frame_sequence: ex_oto_layering_frame_sequence;
    
    keep packet_sequence.driver == driver.packet_driver;
    keep frame_sequence.driver == driver.frame_driver;
};


extend system_driver_u {
    packet_driver : ex_oto_layering_packet_driver_u;
    frame_driver : ex_oto_layering_frame_driver_u;

    event clock is only @sys.any;

    get_sub_drivers(): list of any_sequence_driver is {
        return ({packet_driver; frame_driver});
    }; // get_sub_drivers...
};
'>

o System env definition

<'

unit system_env_u like uvm_env {

    frame_env : ex_oto_layering_frame_env_u is instance;
    packet_env : ex_oto_layering_packet_env_u is instance;
    
    system_driver: system_driver_u is instance;

    keep system_driver.packet_driver == packet_env.agent.driver;
    
    keep system_driver.frame_driver == frame_env.agent.driver;
    
    // binding the layeres together
    keep bind (frame_env.agent.driver.get_item_layer_transfer,
        packet_env.agent.bfm.down_item_layer_transfer);
    keep bind (frame_env.agent.driver.ll_check_do_available,
        packet_env.agent.bfm.ul_check_do_available);
    // binding the frame BFM to the DUT (empty in this example)
    keep bind (frame_env.agent.bfm.d_enable,empty);
    keep bind (frame_env.agent.bfm.d_bus,empty);
};

extend sys {
    system_env : system_env_u is instance;
};

'>
