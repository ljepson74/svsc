/*------------------------------------------------------------------------- 
File name   : xserial_env.e
Title       : Implementation of the env
Project     : XSerial eVC
Created     : 2008
Description : This file contains the implementation of the env.
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
-------------------------------------------------------------------------*/ 

<'

package cdn_xserial;



extend xserial_env_u {
    -- Print a banner for each eVC instance at the start of the test
    show_banner() is also {
        out("(c) Cadence 2002-2006");
        out("eVC instance : ", name);
        out("     ", agent.active_passive);
    }; -- show_banner()
    
    -- Implement the show_status() method
    show_status() is only {
        agent.show_status();
    }; -- show_status()
        
    -- Report the final status at the end of the test.
    finalize() is also {
        message(LOW, "Test done:");
        show_status();
    }; -- finalize()

}; -- extend xserial_env_u

'>


 Configuration

<'
extend xserial_env_u {
    // configure 
    configure( ctr    : uint,
               new_params : xserial_env_config_params_s) is {

        // Propagate config parameters to the agent
        uvm_configure ctr agent {mode} {new_params.mode}; 
          
        // Update local configuraiton parameters
        config.params = new_params.copy();
    };
};

'>


<'
extend xserial_env_u {
     // Configure the transaction recording
    connect_pointers() is also {
        var tr_cfg : recording_config = new;
        
        // Attributes to be collected
        // These are callback attributes - read from the payload
        
        tr_cfg.register_callback_attribute("xserial_frame_s","destination");
        tr_cfg.set_attribute_sampling("xserial_frame_s","destination", 
                                      {ENDED});
        tr_cfg.register_callback_attribute("xserial_frame_s","data");
        tr_cfg.set_attribute_sampling("xserial_frame_s","data", {ENDED});

        assign_recording_config(tr_cfg);
    }; 
};
'>
