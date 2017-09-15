/*------------------------------------------------------------------------- 
File name   : xcore_env.e
Title       : XCore environment
Project     : XCore eVC
Created     : 2008
Description : This file contains the top level unit of the eVC
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide.

-------------------------------------------------------------------------*/ 

<'

package cdn_xcore;


-- This type enumerates the logical names of each instance of the XCore eVC
type xcore_env_name_t : [];

extend tf_domain_t: [XCORE_TF];

unit xcore_env_u like uvm_env {

    tf_testflow_unit;
    keep soft tf_domain == XCORE_TF;
    event tf_phase_clock is only @xbus_evc.synch.clock_rise;

    -- This field provides a screen logger for each eVC instance. 
    -- By default the verbosity is NONE, ie - disabled.
    logger : message_logger is instance;

    -- This field specifies the logical name of this instance of the XCore eVC.
    name : xcore_env_name_t;

    -- This field controls whether the eVC is ACTIVE or PASSIVE
    -- ACTIVE means there is no XCore HDL, and the eVC plays as stand-in
    active_passive : uvm_active_passive_t;

    -- This field specifies whether to perform data and protocol checks
    has_checks : bool;
        keep soft has_checks == TRUE;

    -- This field specifies whether to collect coverage
    has_coverage : bool;
        keep soft has_coverage == TRUE;
        
    -- Pointers to the interface eVCs. These eVCs are to be instantiated in 
    -- the SVE, the simulation & verification environment.
    -- The external eVCs are instantiated in the SVE and not in the eVC.
   
    -- The XBus eVC to which this XCore is connected
    !xbus_evc           : xbus_env_u;
       
    -- The XSerial eVC to which this XCore is connected
    !xserial_evc        : xserial_env_u;
   
    -- The XBus agent representing the XCore
    !xbus_agent : PASSIVE SLAVE xbus_agent_u;


     -- This is the instance of the monitor that monitors all behavior in the
    -- XCore HDL.
    monitor : xcore_monitor_u is instance;
        keep monitor.name == read_only(name);
        keep monitor.has_checks == read_only(has_checks);
        keep monitor.has_coverage == read_only(has_coverage);
     
    -- Shadow registers
    reg_file : XCORE vr_ad_reg_file;
       keep soft reg_file.size == 0x100;

    -- The UVM scoreboard
    bus_to_serial_scbd : xserial_to_xserial_scbd is instance;
    serial_to_bus_scbd : xserial_to_xserial_scbd is instance;

    
    connect_ports() is also {
        -- Using the UVM Scoreboard 
        // eVC xserial agent sending to device
        monitor.xserial_rx_frame_ended_o.connect(serial_to_bus_scbd.add_p);
        
        // device sending to xesrial agent
        monitor.xserial_tx_frame_ended_o.connect(bus_to_serial_scbd.match_p);
    
        do_bind(monitor.tx_frame_written_o, bus_to_serial_scbd.add_p);
        do_bind(monitor.rx_frame_read_o, serial_to_bus_scbd.match_p);
        
        bus_to_serial_scbd.name = append("bus_to_serial_scbd");
        serial_to_bus_scbd.name = append("serial_to_bus_scbd");
    };

    -- This port must be bound to the reset signal of the XCore module.
    sig_reset :  in simple_port of bit is instance;   

    -- This event is emitted at the deassertion of the first reset
    event reset_deassert is cycle @monitor.reset_deassert;    

    -- Updating memory map:

    -- This event emitted on reset_deassert -
    -- after reset XCore base_address has a valid value, hence 
    -- the memory map can be updated accordingly
    -- Upon this event, the upper layer, which holds the memory map, 
    -- should update it
    event update_memory_map;

    wait_for_first_reset : bool;
       keep wait_for_first_reset == TRUE;
    
    on reset_deassert {
        reg_file.reset();
        if wait_for_first_reset then {
            wait_for_first_reset = FALSE;
            emit update_memory_map;
        };
    };

    
    -- Connect to interface eVCs
    
    connect_pointers() is also {
        monitor.reg_file = reg_file;
        reg_file.as_a(XCORE vr_ad_reg_file).monitor =  monitor;

        monitor.xbus_agent_monitor = xbus_agent.agent_monitor;  
        monitor.xserial_rx_monitor = xserial_evc.agent.
                                as_a(has_rx_path xserial_agent_u).rx_monitor;
        monitor.xserial_tx_monitor = xserial_evc.agent.
                                 as_a(has_tx_path xserial_agent_u).tx_monitor;

    }; -- connect_pointers

        
    -- The short_name() method should return the name of this eVC instance.
    short_name(): string is {
        result = append(name);
    };

    -- This controls what color the short name is shown in.
    short_name_style(): vt_style is {
        result = DARK_GREEN;
    };

    -- Print a banner for each instance at the start of the test
    show_banner() is also {
        out("(c) Cadence 2004-2006");
        out("XCore eVC instance: ", name);
    }; -- show_banner()
    
    -- Implement the show_status() method
    show_status() is only {
        out("XCore eVC instance: ", name);
    }; -- show_status()
  

}; -- unit xcore_env_u


'>

<'
extend xcore_monitor_u {

    -- This field allows the monitor to be sub-typed on the name 
    -- of the XCore eVC
    name : xcore_env_name_t;
}; -- extend xcore_monitor_u
'>



<'

// CONFIGURATION:
// --------------

// the macro defines xcore_env_config_u and xcore_env_config_params_s, 
// and instantiates them in xbus_env_u.
uvm_build_config env xcore_env_u xcore_env_config_u xcore_env_config_params_s;

type xcore_mode_t : [NORMAL, FULL_SPEED];

extend xcore_env_u {
    // configure
    configure( ctr        : uint,
               new_params : xcore_env_config_params_s) is {

        -- Propagate config info to sub-components.
        -- Note how each field is not necessary mapped to a single value of 
        -- the lower layer. NORMAL mode in XCore, for example, can cause either
        -- SLOW or NORMAL in the XSerial.
        if new_params.mode == NORMAL then {
            if new_params.max_speed < 500 then {
                uvm_configure ctr xserial_evc  {mode} 
                  {xserial_mode_t'SLOW};
                
            } else {
                uvm_configure ctr xserial_evc  {mode} 
                  {xserial_mode_t'NORMAL};
            };
        } else {
            uvm_configure ctr xserial_evc  {mode} 
              {xserial_mode_t'FAST};
        };

        // update 
        config.params = new_params.copy();        
    }; -- configure

}; -- extend xcore_env_u 


// This unit and its fields are only for the sake of demonstrating the 
// configuration and reconfiguration process. They have no effect on the test.
extend xcore_env_config_params_s {
    mode      : xcore_mode_t;
    max_speed : uint;
};

'>


   Objection to TEST_DONE:
   
   After all sequences drop their objection to TEST_DONE, there is a need 
   to allow the test to continue for some amount of time, to give the XCore 
   time to respond to the last sequence. 
   
   The postpone_end_of_test() has to be called from the top most unit, the 
   unit holding all drivers under it.
   
<'
extend xcore_env_u {
   
    -- The XCore uses the XBus clock for general purposes
    event xbus_clock is @xbus_evc.synch.clock_rise;
   
    drain_time : uint;
        keep soft drain_time == 200;

    in_drain_time : bool;
        keep in_drain_time == FALSE;
     
    postpone_end_of_test() @xbus_clock is {
       if not in_drain_time {
          in_drain_time = TRUE;
          raise_objection(TEST_DONE);
          wait [drain_time] * cycle;
          drop_objection(TEST_DONE);
       }; -- if not in_drain_time
       
    }; -- postpone_end_of_test
   
 }; -- extend xcore_env_u
'>
