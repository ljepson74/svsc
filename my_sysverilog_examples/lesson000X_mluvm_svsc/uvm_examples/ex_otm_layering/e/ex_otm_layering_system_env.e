/*----------------------------------------------------------    
File name   : ex_otm_layering_system_env.e
Title       : Defines the system env 
Project     : one to many layering example
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


extend MAIN ex_otm_layering_packet_sequence {    
    keep soft count == 0;
};


extend MAIN ex_otm_layering_atm_sequence {
    keep soft count == 0;
};

'>

o The virtual sequence definition

<'
sequence system_sequence using created_driver = system_driver_u;

extend system_sequence {
    !packet_sequence: ex_otm_layering_packet_sequence;
    !atm_sequence: ex_otm_layering_atm_sequence;
    
    keep packet_sequence.driver == driver.packet_driver;
    keep atm_sequence.driver == driver.atm_driver;
};


extend system_driver_u {
    packet_driver : ex_otm_layering_packet_driver_u;
    atm_driver : ex_otm_layering_atm_driver_u;

    event clock is only @sys.any;

    get_sub_drivers(): list of any_sequence_driver is {
        return ({packet_driver; atm_driver});
    }; // get_sub_drivers...
};
'>

o System env definition

<'

unit system_env_u like uvm_env {

    atm_env : ex_otm_layering_atm_env_u is instance;
    packet_env : ex_otm_layering_packet_env_u is instance;
    
    system_driver: system_driver_u is instance;

    keep system_driver.packet_driver == packet_env.agent.driver;
    
    keep system_driver.atm_driver == atm_env.agent.driver;
    
    // binding the layeres together
    keep bind (atm_env.agent.driver.get_item_layer_transfer,
               packet_env.agent.bfm.down_item_layer_transfer);
};

// dummy unit for demonstration purpose
unit dut_u {
    back_pressure: out simple_port of byte is instance; // DUT port    
    d_enable: in simple_port of bit is instance; // DUT port
    d_bus: in simple_port of byte is instance;   // DUT port
};

extend sys {
    system_env : system_env_u is instance;
    dut : dut_u is instance;    
    // binding the atm BFM to the DUT (empty in this example)
    keep bind (system_env.atm_env.agent.bfm.d_enable,dut.d_enable);
    keep bind (system_env.atm_env.agent.bfm.d_bus,dut.d_bus);
    keep bind (system_env.atm_env.agent.bfm.back_pressure,dut.back_pressure);
};

'>
