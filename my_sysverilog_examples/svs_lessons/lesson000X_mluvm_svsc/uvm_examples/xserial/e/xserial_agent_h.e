/*------------------------------------------------------------------------- 
File name   : xserial_agent_h.e
Title       : Agent unit public interface
Project     : XSerial eVC
Created     : 2008
Description : This file declares the public interface of the agent unit.
Notes       : Because the agent handles both the TX and RX parts of a link,
            : the 'has_tx_path' and 'has_rx_path' fields are used to
            : sub-type the agent so that the TX and RX paths can be
            : separately disabled. 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
------------------------------------------------------------------------*/ 

<'

package cdn_xserial;


-- This unit represents the eVCs main agent. An agent handles one
-- bidirectional XSerial link.
unit xserial_agent_u like uvm_agent {
    tf_testflow_unit;

    // This unit, and all other units under it, are part of the 
    // XSERIAL_TF domain
    keep soft tf_domain == XSERIAL_TF;

    -- This field provides a screen logger for each eVC instance. By default,
    -- it's verbosity is set to NONE so that it is disabled.
    logger : message_logger is instance;
        keep soft logger.verbosity == NONE;
        keep soft logger.tags == {TESTFLOW_EX};

    -- This field holds the logical name of the eVC instance this agent is
    -- contained in
    name : xserial_env_name_t;
        
    -- This field holds the signal name of the TX_CLOCK signal on the
    -- XSERIAL interface.
    sig_tx_clock : out simple_port of bit is instance;

    -- This field holds the signal name of the TX_DATA signal on the
    -- XSERIAL interface.
    sig_tx_data  :  out simple_port of bit is instance;

    -- This field holds the signal name of the RX_CLOCK signal on the
    -- XSERIAL interface.
    sig_rx_clock :  out simple_port of bit is instance;

    -- This field holds the signal name of the RX_DATA signal on the
    -- XSERIAL interface.
    sig_rx_data  :  out simple_port of bit is instance;
    
    -- This field holds the signal name of the RESET signal on the XSERIAL
    -- interface. 
    sig_reset : inout simple_port of bit is instance;
    
    -- This field controls the active level of the RESET signal. 
    -- By default, the reset is active high, but by constraining this 
    -- field to 0, it can be set to active low.
    reset_active_level : bit;
        keep soft reset_active_level == 1;
    
    -- This field determines what reset state the eVC starts in at the
    -- beginning of a test. By default, the eVC assumes that reset is
    -- asserted at the start of a test. The reset_asserted field goes to 
    -- FALSE at the first de-assertion of the reset signal. 
    reset_asserted : bool;
        keep soft reset_asserted == TRUE;
    
    keep soft active_passive == ACTIVE;
        

    -- If this field is TRUE then the agent does protocol checking on the
    -- tx_data signal.
    check_tx_protocol : bool;
        keep soft check_tx_protocol == TRUE;

    -- If this field is TRUE then the agent does protocol checking on the
    -- rx_data signal.
    check_rx_protocol : bool;
        keep soft check_rx_protocol == TRUE;

    -- This field controls whether coverage information should be 
    -- collected for this agent
    has_coverage : bool;
        keep soft has_coverage == TRUE;
    

    -- This field controls the period of the TX clock in simulator time
    -- units. If this field is 0, then the eVC does not generate the clock.
    -- Note that this field is only used if the agent is ACTIVE and has a
    -- tx path. It is recommended that this field be constrained using 
    -- physical time units
    -- e.g.: keep tx_clock_period == 20 ns; This ensures that there is no
    -- dependency on the simulator time resolution.
    tx_clock_period : time;
        keep soft tx_clock_period == 0;
                                    
    -- If this field is not "" then the agent writes a log file of that
    -- name with a .elog extension. This log file contains all TX
    -- transactions. If both this field and rx_log_filename are the
    -- same then both TX and RX log information will be written to a
    -- single file.
    tx_log_filename : string;
        keep soft tx_log_filename == "xserial";
        
    -- If this field is not "" then the agent writes a log file of that
    -- name with a .elog extension. This log file contains all RX
    -- transactions. If both this field and tx_log_filename are the
    -- same then both TX and RX log information will be written to a
    -- single file.
    rx_log_filename : string;
        keep soft rx_log_filename == "xserial";
        
    
    -- This field is set to the frame just transmitted just before the
    -- tx_frame_done event is emitted.
    !tx_frame : MONITOR xserial_frame_s;
    
    -- This field is set to the frame just received just before the
    -- rx_frame_done event is emitted.
    !rx_frame : MONITOR xserial_frame_s;
    
    -- This event gets emitted each time a frame is transmitted.
    event tx_frame_done;
    
    -- This event gets emitted each time a frame is transmitted.
    event rx_frame_done;
    
    -- This event gets emitted when reset is asserted.
    event reset_start;
    
    -- This event gets emitted when reset is de-asserted. 
    event reset_end;

    -- This field is used to sub-type the agent for when the TX path is
    -- enabled.
    const has_tx_path : bool;
       keep soft has_tx_path;

    -- This field is used to sub-type the agent for when the RX path is
    -- enabled.
    const has_rx_path : bool;
       keep soft has_rx_path;
}; -- unit xserial_agent_u

extend xserial_monitor_u {
    -- This field is a back-pointer to the agent that contains the monitor.
    !agent : xserial_agent_u;

}; -- extend xserial_monitor_u


extend xserial_bfm_u {
    -- This field is a back-pointer to the agent that contains the BFM.
    !agent : xserial_agent_u;

}; -- extend xserial_bfm_u


extend has_tx_path xserial_agent_u {

    event tf_phase_clock is only @tx_monitor.unqualified_clock_rise;
   
    -- This field is the instance of the monitor for the transmit direction.
    -- It only exists if the TX direction is enabled for this agent.
    tx_monitor : TX xserial_monitor_u is instance;
        keep tx_monitor.file_logger.to_file == read_only(tx_log_filename);
        keep tx_monitor.has_protocol_checker == 
                        read_only(check_tx_protocol);
        keep tx_monitor.has_coverage == has_coverage;
    
    connect_pointers() is also {
        tx_monitor.agent = me;
    };
    
    keep tx_monitor.collector.sig_clock.hdl_path() ==
                         read_only(sig_tx_clock.hdl_path());
    keep tx_monitor.collector.sig_data.hdl_path() ==
                       read_only(sig_tx_data.hdl_path());
    
}; -- extend has_tx_path xserial_agent_u


extend has_rx_path xserial_agent_u {
        
    -- This field is the instance of the monitor for the receive direction.
    -- It only exists if the RX direction is enabled for this agent.
    rx_monitor : RX xserial_monitor_u is instance;
        keep rx_monitor.file_logger.to_file ==
                         read_only(rx_log_filename);
        keep rx_monitor.has_protocol_checker ==
                         read_only(check_rx_protocol);
        keep rx_monitor.has_coverage == has_coverage;

    connect_pointers() is also {
        rx_monitor.agent = me;
    };

    keep rx_monitor.collector.sig_clock.hdl_path() ==
                         read_only(sig_rx_clock.hdl_path());
    keep rx_monitor.collector.sig_data.hdl_path() ==
                         read_only(sig_rx_data.hdl_path());
}; -- extend has_rx_path xserial_agent_u


-- If in ACTIVE mode with TX path enabled, then add a TX BFM and a
-- TX sequence driver.
extend ACTIVE has_tx_path xserial_agent_u {

    -- This field is the instance of the transmit BFM. It only exists if the
    -- TX direction is enabled for this agent and the agent is ACTIVE.
    tx_bfm : xserial_bfm_u is instance;
        keep tx_bfm.driver == read_only(tx_driver);
        keep tx_bfm.tx_monitor == read_only(tx_monitor);

    connect_pointers() is also {
        tx_bfm.agent = me;
    };

    keep tx_bfm.sig_tx_clock.hdl_path() ==
                             read_only(sig_tx_clock.hdl_path());
    keep tx_bfm.sig_tx_data.hdl_path() ==
                             read_only(sig_tx_data.hdl_path());
      
    -- This field is the instance of the transmit sequence driver. It only
    -- exists if the TX direction is enabled for this agent and the agent is
    -- ACTIVE.
    tx_driver : xserial_driver_u is instance;
        keep tx_driver.name == read_only(name);
        
}; -- extend ACTIVE has_tx_path xserial_agent_u


-- If both monitors are present, make them aware of each other.
extend has_rx_path has_tx_path xserial_agent_u {
    connect_pointers() is also {
        tx_monitor.reverse_monitor = rx_monitor;
        rx_monitor.reverse_monitor = tx_monitor;
    }; 

}; -- extend has_rx_path has_tx_path xserial_agent_u


-- If agent is in ACTIVE mode and both paths are enabled, then the Tx BFM 
-- needs to know where the Rx monitor is so it can check on the current
-- state of flow control
extend ACTIVE has_rx_path has_tx_path xserial_agent_u {

    keep tx_bfm.rx_monitor == read_only(rx_monitor);
    
}; -- extend ACTIVE has_rx_path has_tx_path xserial_agent_u


// CONFIGURATION:
// --------------

// the macro instantiates unit xserial_agent_config_u and struct 
// xserial_agent_config_params, in xserial_agent_u.
// if they have no been defined earlier - also defines them
// In this example, xserial_agent_config_u xserial_agent_config_params have
// not been defined earlier, so will be defiend by the uvm_build_config

uvm_build_config agent xserial_agent_u xserial_agent_config_u xserial_agent_config_params;


// parameters to user, for changing configuration during the run
extend xserial_agent_config_params {
    mode : xserial_mode_t;
};

'>

