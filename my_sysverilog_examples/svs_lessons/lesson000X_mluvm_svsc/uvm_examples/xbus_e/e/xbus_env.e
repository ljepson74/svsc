/*-------------------------------------------------------------------------  
File name   : xbus_env.e
Title       : Implementation of top level env unit for UVC
Project     : XBus UVC
Created     : 2008
Description : This file adds implementation details to the env.
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



extend xbus_env_u {

    -- This is a list of pointers to the master signal maps for each master
    -- agent.
    msmps : list of xbus_master_signal_map_u;
        keep msmps == read_only(masters.apply(it.msmp));

    -- This is a list of pointers to the configuration units for each slave
    -- agent.
    slave_configs : list of xbus_slave_config_u;
        keep slave_configs == read_only(slaves.apply(it.config));

    -- Set up required back-pointers and other control fields in each sub-unit.
    keep soft synch.has_checks == read_only(has_checks);
    
    keep bus_monitor.bus_name == read_only(bus_name);
    keep soft bus_monitor.abstraction_level == read_only(abstraction_level);
    keep bus_monitor.synch == read_only(synch); 
    keep bus_monitor.collector.synch == read_only(synch); 
    keep bus_monitor.collector.smp == read_only(smp); 
    keep bus_monitor.collector.msmps == read_only(msmps);
    keep bus_monitor.slave_configs == read_only(slave_configs);
    keep soft bus_monitor.has_checks == read_only(has_checks);
    
    keep for each (master) in active_masters {
        soft master.abstraction_level == read_only(abstraction_level);
        master.smp == read_only(smp);
        master.synch == read_only(synch);
        soft master.agent_monitor.has_checks == read_only(has_checks);
    };
    keep for each (master) in passive_masters {
        soft master.abstraction_level == read_only(abstraction_level);
        master.smp == read_only(smp);
        master.synch == read_only(synch);
        soft master.agent_monitor.has_checks == read_only(has_checks);
    };
    keep for each (slave) in active_slaves {
        soft slave.abstraction_level == read_only(abstraction_level);
        slave.smp == read_only(smp);
        slave.synch == read_only(synch);
        soft slave.agent_monitor.has_checks == read_only(has_checks);
    };
    keep for each (slave) in passive_slaves {
        soft slave.abstraction_level == read_only(abstraction_level);
        slave.smp == read_only(smp);
        slave.synch == read_only(synch);
        soft slave.agent_monitor.has_checks == read_only(has_checks);
    };
    
    keep soft arbiter.abstraction_level == read_only(abstraction_level);
    keep arbiter.smp == read_only(smp);
    keep arbiter.synch == read_only(synch);
    keep arbiter is a ACTIVE ARBITER xbus_agent_u (aaa) =>
        aaa.bfm.msmps == read_only(msmps);
    keep soft arbiter.agent_monitor.has_checks == read_only(has_checks);

    -- Hook up a pointer to the bus monitor in each agent monitor and BFM.
    -- This is done procedurally to avoid an order cycle.
    connect_pointers() is also {
        for each (master) in masters {
            master.agent_monitor.bus_monitor = bus_monitor;
            if master is a ACTIVE MASTER xbus_agent_u (am) {
                am.bfm.bus_monitor = bus_monitor;
                am.bfm.bus_collector = bus_monitor.collector;
            };
        };
        for each (slave) in slaves {
            slave.agent_monitor.bus_monitor = bus_monitor;
            if slave is a ACTIVE SLAVE xbus_agent_u (as) {
                as.bfm.bus_monitor = bus_monitor;                
                as.bfm.bus_collector = bus_monitor.collector;                
            };
        };
        arbiter.agent_monitor.bus_monitor = bus_monitor;
        if arbiter is a ACTIVE ARBITER xbus_agent_u (a) {
            a.bfm.bus_monitor = bus_monitor;
            a.bfm.bus_collector = bus_monitor.collector;
        }; 
    }; -- connect_pointers()

    connect_ports() is also {
        for each (slave) in slaves {
            bus_monitor.transfer_ended_o.connect(
                slave.agent_monitor.transfer_ended_i);
        };        
        for each (master) in masters {
            bus_monitor.transfer_ended_o.connect(
                master.agent_monitor.transfer_ended_i);
        };        
    }; -- connect_ports()
    
    -- The short_name() method should return the name of this UVC instance.
    short_name(): string is {
        result = append(bus_name);
    }; -- short_name()

    -- This method controls what colour the short name is shown in.
    short_name_style(): vt_style is {
        result = DARK_RED;
    }; -- short_name_style()
    
    -- This method shows the current status of the UVC.
    show_status() is only {
        bus_monitor.show_status();
        for each in masters {
            it.agent_monitor.show_status();
        };
        for each in slaves {
            it.agent_monitor.show_status();
        };
    }; -- show_status()

    -- Report the final status at the end of the test.
    finalize() is also {
        message(LOW, "Test done:");
        show_status();
    }; -- finalize()

    -- This method prints a banner for each UVC instance at the start of the
    -- test.
    show_banner() is also {
        out("(c) Cadence 2002-2005");
        out("Bus : ", bus_name);
        out("     ", 
            dec(masters.count(.active_passive == ACTIVE)), 
            " ACTIVE masters");
        out("     ", 
            dec(masters.count(.active_passive == PASSIVE)), 
            " PASSIVE masters");
        out("     ", 
            dec(slaves.count(.active_passive == ACTIVE)), 
            " ACTIVE slaves");
        out("     ", 
            dec(slaves.count(.active_passive == PASSIVE)), 
            " PASSIVE slaves");
        if arbiter.active_passive == ACTIVE {
            out("     ACTIVE arbiter");
        } else {
            out("     PASSIVE arbiter");
        };
    }; -- show_banner()
    
    
    
    // Configure the transaction recording
    connect_pointers() is also {
        var tr_cfg : recording_config = new;
        
        tr_cfg.register_field_attributes("xbus_trans_s",
                                         {"read_write"; "addr";} );
        
        tr_cfg.register_callback_attribute("xbus_slave_response_s",
                                           "read_write");
        tr_cfg.register_callback_attribute("xbus_slave_response_s",
                                           "addr");

        assign_recording_config(tr_cfg);
    };
    
}; -- extend xbus_env_u

'>


 Configuration

<'
extend xbus_env_u {
    
    // configure
    configure( ctr    : uint,
               new_params : xbus_env_config_params_s) is {
        
        // Update local parameters, if required
        // Currently - empty 
        
        // Propagate values to agent
        for each (slave) in slaves {
             if slave.agent_name == new_params.slave_name {
                 uvm_configure ctr slave {min_addr;     max_addr} 
                                      {new_params.min_addr; new_params.max_addr};
        
             };
        };
        config.params = new_params.copy();
    }; -- configure
}; -- xbus_env_u


'>

