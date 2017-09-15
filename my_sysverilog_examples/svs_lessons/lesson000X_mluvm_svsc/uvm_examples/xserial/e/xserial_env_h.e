/*------------------------------------------------------------------------- 
File name   : xserial_env_h.e
Title       : Env unit public interface
Project     : XSerial eVC
Created     : 2008
Description : This file contains the declaration of the env unit and all
            : user accessible fields, events and methods. 
Notes       : In this eVC, there is only a single agent per env. An env
            : should contain all agents that logically belong to the same
            : "network". In the case of the XSerial protocol, a network
            : consists only of two devices linked bidirectionally. Because
            : all the behaviour of one device can be deduced by looking at
            : the signals at the other device, there is no need to have a
            : passive agent monitoring the other end of the link. As such,
            : only a single agent is ever required per env.
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
-------------------------------------------------------------------------*/ 

<'

package cdn_xserial;

-- This unit is the env - the top level unit of the eVC.
unit xserial_env_u like uvm_env {
    tf_testflow_unit;
    keep soft tf_domain == XSERIAL_TF;
    // By default - run all phases on sys.any. 
    // If required - override by conecting to another clock
    event tf_phase_clock is only @sys.any;
   
    
    -- This field provides a screen logger for the env. Note that this eVC
    -- has only a single agent per env, so there is no point adding a
    -- separate screen logger for each agent.
    logger : message_logger is instance;
        keep soft logger.verbosity == NONE;
    
    -- This field holds the logical name of this eVC instance.
    name : xserial_env_name_t;    
    
    -- This field is used to sub-type the agent for when the TX path is
    -- enabled.
    const has_tx_path : bool;
       keep soft has_tx_path;

    -- This field is used to sub-type the agent for when the RX path is
    -- enabled.
    const has_rx_path : bool;
       keep soft has_rx_path;

    -- This field is the instance of the agent. Note that each env (eVC
    -- instance) has just one agent that handles both Tx and Rx directions.
    agent : xserial_agent_u is instance;
        keep agent.name == read_only(name);
        keep type agent.has_tx_path == has_tx_path;
        keep type agent.has_rx_path == has_rx_path;
        
}; -- unit xserial_env_u

'>


Status report:

<'
extend xserial_env_u {
    
    -- Print a banner for each eVC instance at the start of the test
    show_banner() is also {
        out("(c) Cadence 2002-2006");
        out("eVC instance : ", name);
        out("     ", agent.active_passive);
    }; -- show_banner()

    
    -- The short_name() method should return the name of this eVC instance.
    short_name(): string is {
        result = append(name);
    };

    -- This controls what colour the short name is shown in.
    short_name_style(): vt_style is {
        result = DARK_CYAN;
    };
    
    -- Implement the show_status() method
    show_status() is {
        agent.show_status();
    }; -- show_status()

    -- Report the final status at the end of the test.
    finalize() is also {
        message(LOW, "Test done:");
        show_status();
    }; -- finalize()
};    



// CONFIGURATION:
// --------------

// the macro defines xserial_env_config_u and xserial_env_config_params_s, 
// and instantiates them in xserial_env_u.
uvm_build_config env xserial_env_u xserial_env_config_u xserial_env_config_params_s;

// This parameter is for the sake of demonstrating configuartion propagation
// It has no real effect on the run
extend xserial_env_config_params_s {
    mode : xserial_mode_t;
};
'>
