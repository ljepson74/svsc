/*------------------------------------------------------------------------- 
File name   : xcore_xbus_config.e
Title       : XSerial eVC configuration
Project     : Xcore eVC
Created     : 2008
Description : Configures XBus eVC for testing Xcore
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide.
-------------------------------------------------------------------------*/ 

<'

package cdn_xcore;

extend xbus_bus_name_t   : [XCORE_XBUS];
extend xbus_agent_name_t : [XCORE_XBUS_AGENT];
  
'>

   
   
   Configurate the XBus eVC
   
   Using soft constraints, so can be overwritten in the SVE
   
<'

extend xbus_signal_map_u {    
    keep sig_data.verilog_wire() == TRUE;
    keep sig_data.declared_range() == "[7:0]";
};


extend xbus_env_u {

    -- Define the XBus agents that build the environment
    -- Default verification environment:
    --   One eVC active master
    --   One passive slave (== DUT)
    --   One eVC arbiter
    keep soft active_master_names  == {XCORE_XBUS_AGENT};
    keep soft passive_master_names == {};
    keep soft active_slave_names   == {};
    keep soft passive_slave_names  == {XCORE_XBUS_AGENT };
    keep soft arbiter is a 
              XCORE_XBUS_AGENT ACTIVE ARBITER xbus_agent_u;
    
    keep soft has_checks == TRUE;
    
    keep soft bus_monitor.log_filename == "XCORE_XBUS";
    keep soft active_masters[0].agent_monitor.log_filename == 
              "XCORE_XBUS_MASTER";
    keep soft passive_slaves[0].agent_monitor.log_filename == 
                                "XCORE_XBUS_SLAVE";

 
 }; --

extend xcore_monitor_u {
    -- As reset is deasserted, sample the base_address from the HDL.    
    on reset_deassert {
        base_address = (sig_base_addr$).as_a(uint(bits:16)) * 0x100;
        
        var new_min_addr := base_address + 0x0000;
        var new_max_addr := base_address + 0x00ff;
        uvm_configure 1 get_enclosing_unit(xcore_env_u).xbus_evc
              {slave_name;  min_addr; max_addr} 
          {xbus_agent_name_t'XCORE_XBUS_AGENT; new_min_addr; new_max_addr};
    };
};
'>
   
