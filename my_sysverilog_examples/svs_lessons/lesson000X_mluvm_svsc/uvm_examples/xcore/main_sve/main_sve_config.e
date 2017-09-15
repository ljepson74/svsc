----------------------------------------------------------------------------
----------------------------------------------------------------------------

File name    : main_sve_config.e
Title        : XCore eVC demo - configuration
Project      : XCore eVC
Created On   : March 2004
Description  : This file demonstrates integration of the insantiations of
             : the XBus, XSerial and XCore eVCs to form a deliverable 
             : testbench env for the XCore module.
             :
             : This configuration is for the sample device
Notes        : 
----------------------------------------------------------------------------
>>>>>>>>>>>>>>>>>>>>>>>>>>> COPYRIGHT NOTICE <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
----------------------------------------------------------------------------
Copyright (c) 2006-2010 Cadence Design Systems,
Inc.All rights reserved worldwide.

----------------------------------------------------------------------------
Revision History :
----------------------------------------------------------------------------

<'

import xcore/e/xcore_top;
import xbus_e/e/xbus_port_config;
import xserial/e/xserial_port_config;
import xcore/e/xcore_port_config;

// workarounds and patches
import main_sve_patches.e;

extend xcore_env_name_t : [XCORE_SVE];

extend sys {
    xcore_sve : xcore_sve_u is instance;
}; 
'>
   
   Instantiate all environment components:
                eVCs, memory, drivers

<'
unit xcore_sve_u like uvm_env {
   
    keep hdl_path()           == "xcore_tb";

    xcore_evc : PASSIVE XCORE_SVE xcore_env_u is instance;
      keep xcore_evc.hdl_path() == "xcore";


    -- The instance of the XBus eVC
    xbus_evc :  XCORE_XBUS xbus_env_u is instance;


    -- The instance of the XSerial eVC
    xserial_evc : XCORE_XSERIAL has_tx_path has_rx_path 
                                                  xserial_env_u is instance;
    

    -- Registers address map
    xcore_addr_map : vr_ad_map;  


    -- The virtual sequence driver, controlling all the drivers
    virtual_seq_driver : xcore_virtual_driver is instance;

    reg_driver: vr_ad_sequence_driver is instance;
      keep reg_driver.addr_map == value(xcore_addr_map);
      keep reg_driver.default_bfm_sd == xbus_evc.active_masters[0].driver;
   
   
    -- Connect the pointers, connect eVCs to each other
    
    connect_pointers() is also {
        xcore_evc.xbus_evc = xbus_evc;
        xcore_evc.xserial_evc = xserial_evc;
        xcore_evc.xbus_agent = xbus_evc.passive_slaves[0];
        
        virtual_seq_driver.xcore_regs_driver = reg_driver;
        virtual_seq_driver.xserial_driver = xserial_evc.agent.
          as_a(ACTIVE has_tx_path xserial_agent_u).tx_driver;
        virtual_seq_driver.xbus_driver = xbus_evc.active_masters[0].driver;

    }; -- connect_pointers()
    
}; -- unit xcore_sve_u

'>
  
   
   XCore registers file and address map

   When the XCore eVC informs that all data is valid - add the XCore registers
   file to the memory map.

<'
extend xcore_sve_u {   
    event update_memory_map is @xcore_evc.update_memory_map;
    
    on update_memory_map {
        -- Add the XCore registers to the address map
        xcore_addr_map.add_with_offset(xcore_evc.monitor.base_address,
                                       xcore_evc.reg_file);
    }; 
}; 



-- SVE address map and registers driver
extend xcore_sve_u {

    post_generate() is also {
        -- Give all registers in the shadow registers their reset value
        xcore_addr_map.reset();
    }; 
    
    get_addr_map() : vr_ad_map is {
        result = xcore_addr_map;
    };
    
    event device_reset_done is @xcore_evc.reset_deassert;
    
    // The vr_ad does not participate in the testflow, in this eVC,
    // so we have to add the synhcronization with reest.
    // If vr_ad uses the testflow, no need for this synch
    on device_reset_done {
        emit reg_driver.device_reset_done;
    }; 

}; -- extend xcore_sve_u 
'>
   
   Objection to TEST_DONE:
   
   After all sequences drop their objection to TEST_DONE, there is a need 
   to allow the test to continue for some amount of time, to give the XCore 
   time to repsond to the last sequence. 

<'
extend xcore_sve_u {
    all_objections_dropped(kind : objection_kind) is also {
       if kind == TEST_DONE then {
          start xcore_evc.postpone_end_of_test();
       }; 
    };     
 }; 
'>


  Controlling the sequences:

  In this environment, most of the scenarios are to be created by the virtual 
  sequnce driver, which controls the BFM drivers.

<'
extend MAIN xbus_master_sequence {
    keep soft count == 0;
}; 

extend MAIN xserial_sequence {
    keep soft count == 0;
};


extend MAIN vr_ad_sequence {
    keep soft count == 0;
}; 

'>

Configuration of Specman

<'
extend sys {
    init() is also {
        // Use a performance enhancement feature
        set_config(simulation, enable_ports_unification, TRUE); 
    };
    
    run() is also {
        // Ignore the messages from the vr_ad
        specman("set message -remove @vr_ad*");
    };
};
'>
