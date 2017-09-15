/*------------------------------------------------------------------------- 
File name   : xserial_config.e
Title       : XSerial eVC example config file
Project     : XSerial eVC
Created     : 2008
Description : Provides XSerial eVC configuration that is common to all test
            : cases.
Notes       : The DUT for this demonstration verification environment is
            : a 3 input, 3 output router. See the EXAMPLES_README file
            : for more info.
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
-------------------------------------------------------------------------*/ 

<'

-- Import the XSerial eVC
import xserial/e/xserial_top;

import xserial/e/xserial_port_config;

-- Create a logical name for each eVC instance. 
extend xserial_env_name_t : [XSERIAL_A, XSERIAL_B, XSERIAL_C];

-- Instantiate the eVC instances under sys.
extend sys {
    xserial_evcs[3] : list of xserial_env_u is instance;
    keep for each in xserial_evcs {
        index == 0 => it is a XSERIAL_A xserial_env_u;
        index == 1 => it is a XSERIAL_B xserial_env_u;
        index == 2 => it is a XSERIAL_C xserial_env_u;
    };
};

-- There are only three destination ports on the router
extend xserial_frame_payload_s {
    keep destination in [0..2];
}; -- extend xserial_frame_payload_s

-- Configure each eVC instance. This section sets up how the eVC accesses
-- signals in the DUT.

extend XSERIAL_A xserial_env_u {
    keep hdl_path() == "xserial_evc_demo";
};

extend XSERIAL_B xserial_env_u {
    keep hdl_path() == "xserial_evc_demo";
};

extend XSERIAL_C xserial_env_u {
    keep hdl_path() == "xserial_evc_demo";
};


extend XSERIAL_A xserial_agent_u {
    -- eVC does not drive clock
    keep tx_clock_period == 0;
    -- These are the signal names for this agent
    keep sig_tx_clock.hdl_path() == "clock";
    keep sig_tx_data.hdl_path()  == "port_a_in_data";
    keep sig_rx_clock.hdl_path() == "clock";
    keep sig_rx_data.hdl_path()  == "port_a_out_data";
    keep sig_reset.hdl_path()    == "reset";
    keep reset_active_level      == 1;
};

extend XSERIAL_B xserial_agent_u {
    -- eVC does not drive clock
    keep tx_clock_period == 0;
    
    -- These are the signal names for this agent
    keep sig_tx_clock.hdl_path() == "clock";
    keep sig_tx_data.hdl_path()  == "port_b_in_data";
    keep sig_rx_clock.hdl_path() == "clock";
    keep sig_rx_data.hdl_path()  == "port_b_out_data";
    keep sig_reset.hdl_path()    == "reset";
    keep reset_active_level      == 1;
};

extend XSERIAL_C xserial_agent_u {
    -- eVC does not drive clock
    keep tx_clock_period == 0;
    
    -- These are the signal names for this agent
    keep sig_tx_clock.hdl_path() == "clock";
    keep sig_tx_data.hdl_path()  == "port_c_in_data";
    keep sig_rx_clock.hdl_path() == "clock";
    keep sig_rx_data.hdl_path()  == "port_c_out_data";
    keep sig_reset.hdl_path()    == "reset";
    keep reset_active_level      == 1;
};


-- Turn on logging for all agents. Use env name for log filenames.
extend xserial_agent_u {
    keep tx_log_filename == append(name, "_tx");
    keep rx_log_filename == append(name, "_rx");
}; 



'>

<'
extend sys {
    init() is also {
        // Use a performance enhancement feature
        set_config(simulation, enable_ports_unification, TRUE);   
    };
};
'>
