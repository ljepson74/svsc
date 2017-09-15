/*------------------------------------------------------------------------- 
File name   : xbus_arbiter_dut_accel_config.e
Title       : XBus eVC example configuration file
Project     : XBus eVC
Created     : 2011
Description : This file provides XBus eVC configuration that is common to
            : all test cases.
Notes       : 
--------------------------------------------------------------------------- 
//----------------------------------------------------------------------
//   Copyright 2008-2010 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------
-------------------------------------------------------------------------*/ 


<'
#ifdef SPECMAN_VERSION_10_2_OR_LATER {
} 
#else {
   import msg_patch;
};

'>

<'

-- Import the XBus eVC
import xbus_e/e/xbus_top;

// support running on acceleration
import xbus_e/e/xbus_accel;

import xbus_e/e/xbus_port_config;

-- Create a logical name for the eVC instance. 
extend xbus_bus_name_t : [XBUS];

-- Instantiate the eVC under sys.
extend sys {
    xbus_evc : XBUS xbus_env_u is instance;
};

-- Create a logical name for each agent in the bus (including both ACTIVE and
-- PASSIVE agents).

extend xbus_agent_name_t : [MASTER_0, 
                            SLAVE_0, 
                            ARB_0];

-- Instantiate the agents under the eVC instance
extend XBUS xbus_env_u {
    keep hdl_path()     == "xbus_tb_top.dut";
    keep abstraction_level == UVM_ACCEL;
    keep passive_master_names == {};
    keep active_master_names  == {MASTER_0}; 
    keep passive_slave_names  == {};
    keep active_slave_names   == {SLAVE_0}; 
    
    -- The arbiter agent is called ARB_0 and is ACTIVE
    keep arbiter is a ARB_0 PASSIVE ARBITER xbus_agent_u;
    -- This instance of the eVC has a protocol checker
    keep has_checks == TRUE;
};


extend XBUS xbus_signal_map_u {
    keep hdl_path() == "xi0";
    keep sig_start.hdl_path() == "sig_start";
    keep sig_addr.hdl_path()  == "sig_addr";
    keep sig_size.hdl_path()  == "sig_size";
    keep sig_read.hdl_path()  == "sig_read";
    keep sig_write.hdl_path() == "sig_write";
    keep sig_bip.hdl_path()   == "sig_bip";
    keep sig_wait.hdl_path()  == "sig_wait";
    keep sig_error.hdl_path() == "sig_error";
    keep sig_data.hdl_path()  == "sig_data_out";  
};
extend XBUS xbus_synchronizer_u {
    keep sig_clock.hdl_path() == "clk";
    keep sig_reset.hdl_path() == "rst";
    
    keep sig_reset.verilog_wire() == TRUE;
};
extend MASTER_0 xbus_master_signal_map_u {
    keep sig_request.hdl_path() == "sig_request[0]";
    keep sig_grant.hdl_path()   == "sig_grant[0]";
};
-- Configure SLAVE_0
extend XBUS SLAVE_0 xbus_slave_config_u {
    -- This slave responds to address in the range [0x0000..0x7fff] inclusive
    keep params.min_addr == 0x0000;
    keep params.max_addr == 0x7fff;
};



-- Turn on logging for all agents and for whole bus. Use agent and env names
-- for log filenames.
extend xbus_bus_monitor_u {
    keep log_filename == append(bus_name);
};
extend xbus_agent_monitor_u {
    keep log_filename == append(agent_name);
};

extend sys {
    setup() is also {
        set_config(print, radix, hex);
    };
    init() is also {
        // Use a performance enhancement feature
        set_config(simulation, enable_ports_unification, TRUE);   
    };
};


extend MASTER_0 MAIN MAIN_TEST xbus_master_sequence {
    keep soft count == 0;
};


'>
