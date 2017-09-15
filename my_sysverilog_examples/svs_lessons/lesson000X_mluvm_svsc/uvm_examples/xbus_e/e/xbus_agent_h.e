/*-------------------------------------------------------------------------  
File name   : xbus_agent_h.e
Title       : Agent unit declaration
Project     : XBus UVC
Created     : 2008
Description : This file declares the agent unit.
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

package cdn_xbus;
     
     

-- This unit is the base type for all agents (masters, slaves and arbiters)
-- that are connected to the bus.
unit xbus_agent_u like uvm_agent {

    tf_testflow_unit;
    
    -- This unit and all units under it belong to the XBUS_TF
    -- TestFlow domain
    keep soft tf_domain == XBUS_TF;
    event tf_phase_clock is only @synch.unqualified_clock_rise;

    -- This field holds the abstraction level:
    -- UVM_SIGNAL, UVM_TLM, UVM_ACCEL, UVM_SIGNAL_SC
    abstraction_level : uvm_abstraction_level_t;
      keep soft abstraction_level == UVM_SIGNAL;
    
    -- This field provides a screen logger for each UVC instance. By default,
    -- it's verbosity is set to NONE so that it is disabled.
    logger : message_logger is instance;
        keep soft logger.verbosity == NONE;
        keep soft logger.tags == {TESTFLOW_EX};
      
    -- This field is the logical name of the bus the agent is connected to.
    -- This field is automatically constrained by the UVC and should not be
    -- constrained by the user.
    bus_name : xbus_bus_name_t;

    -- This field is the logical name of the agent. This field is
    -- automatically constrained by the UVC and should not be constrained by
    -- the user.
    agent_name : xbus_agent_name_t;
    
    -- This field controls what sort of agent this is (MASTER, SLAVE or
    -- ARBITER). This field is automatically constrained by the UVC and should
    -- not be constrained by the user.
    const kind : xbus_agent_kind_t;

    agent_monitor : xbus_agent_monitor_u is instance;
       keep agent_monitor.bus_name == read_only(bus_name);
       keep agent_monitor.agent_name == read_only(agent_name);
       keep agent_monitor.kind == read_only(kind);
       keep agent_monitor.agent == read_only(me);
       keep agent_monitor.abstraction_level == read_only(abstraction_level);

    
    -- This field is a pointer to the synchronizer.
    synch : xbus_synchronizer_u;
    
    -- This field is a pointer to the bus signal map.
    smp : xbus_signal_map_u;

    -- This method gets called by the env to rerun the agent. It is extended in
    -- the various sub-types to ensure that the appropriate units get rerun().
    do_rerun() is {
        agent_monitor.rerun();
    }; -- do_rerun()


    -- The short_name() method should return the name of this agent instance.
    short_name(): string is {
        result = append(agent_name);
    }; -- short_name()    
}; -- unit xbus_agent_u

'>



 Add agent to other units

<'
extend  xbus_agent_monitor_u {
    -- This field is a back-pointer to the agent this monitor is for.
    package agent : xbus_agent_u;
};
'>


<'
extend xbus_master_signal_map_u {

    -- This field is a pointer to the MASTER agent that uses this signal map.
    master : MASTER xbus_agent_u;
    
}; -- extend xbus_master_signal_map_u
'>


  Configuration 

<'
// the macro instantiates unit xserial_agent_config_u and struct 
// xserial_agent_config_params, in xserial_agent_u.
// In this example, xserial_agent_config_u xserial_agent_config_params have
// been defined earlier (in xbus_types_h.e)

uvm_build_config agent a SLAVE xbus_agent_u xbus_slave_config_u xbus_slave_params;


extend xbus_slave_config_u {
    slave : SLAVE xbus_agent_u;
};

extend SLAVE xbus_agent_u {
    keep config.bus_name == read_only(bus_name);
    keep config.slave_name == read_only(agent_name);
    keep config.slave == read_only(me);
};

extend xbus_slave_config_u {
    -- This method takes an address and returns TRUE if that address is within
    -- the range that this slave responds to (as defined by min_addr and
    -- max_addr).
    in_range(addr : xbus_addr_t) : bool is {
        result = (addr >= params.min_addr) and (addr <= params.max_addr);
    }; -- in_range()    
};
'>

