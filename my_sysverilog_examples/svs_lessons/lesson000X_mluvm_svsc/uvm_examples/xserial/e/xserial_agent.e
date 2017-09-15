/*------------------------------------------------------------------------- 
File name   : xserial_agent.e
Title       : Agent unit implementation
Project     : XSerial eVC
Created     : 2008
Description : This file contains all the fields and methods of the agent
            : unit that are not exposed to the user. 
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
-------------------------------------------------------------------------*/ 

<'

package cdn_xserial;

-- Add stuff to the agent which is generic to all directions.
extend xserial_agent_u {

    -- This field indicates whether there is a reset signal in the DUT
    has_reset : bool;
        keep soft has_reset == TRUE;
        
    -- Ensure that the reset_asserted field is kept up-to-date.
    on reset_start { 
        reset_asserted = TRUE;
        message(LOW, "Reset was asserted");
    };
    on reset_end { 
        reset_asserted = FALSE;
        message(LOW, "Reset was de-asserted");
    };

    -- This method gets called whenever reset is re-asserted during a test.
    -- It performs all actions necessary to get this instance of the eVC
    -- back into a reset state.
    
    -- This method returns a string that indicates context. It is used
    -- during error reporting.
    package error_header() : string is {
        result = append("XSerial eVC, Agent: ", name);
    }; -- err_header()
    
    -- This method reports the current status of the agent.
    show_status() is empty;
    
    
}; -- extend xserial_agent_u


-- Define reset_start and reset_end events where the reset signal is in use.
extend has_reset xserial_agent_u {

    -- Hook up the reset_start and reset_end events to the signal in
    -- the DUT.
    private event reset_change is change(sig_reset$) @sim;
    event reset_start is only
        true((not reset_asserted) and
             (sig_reset$ == reset_active_level)) @reset_change;
    event reset_end  is only
        true(reset_asserted and
             (sig_reset$ != reset_active_level)) @reset_change;
    
}; -- extend has_reset xserial_agent_u


-- Rerun TX monitor if reset gets re-asserted during the test.
extend has_tx_path xserial_agent_u {

    show_status() is also {
        tx_monitor.show_status();
    }; -- show_status()
    
}; -- extend has_tx_path xserial_agent_u


-- Rerun RX monitor if reset gets re-asserted during the test.
extend has_rx_path xserial_agent_u {
    show_status() is also {
        rx_monitor.show_status();
    }; -- show_status()

}; -- extend has_rx_path xserial_agent_u


-- Add in stuff required when agent has an ACTIVE tx path.
extend ACTIVE has_tx_path xserial_agent_u {

    private connect_driver_clock() @tx_monitor.clock_rise is {
        while TRUE {
            emit tx_driver.clock; 
            wait cycle;
        };
    }; -- connect_driver_clock()
    
    run() is also {
        start connect_driver_clock();
    }; -- run()


    -- Rerun TX BFM if reset gets re-asserted during the test.
        
    -- ACTIVE agents with a TX path also have the optional ability to
    -- generate the clock.
    private drive_clock() @sys.any is {
        var half_period : time;
        half_period = tx_clock_period / 2;
        while TRUE {
            sig_tx_clock$ = 1;
            wait delay (half_period);
            sig_tx_clock$ = 0;
            wait delay (tx_clock_period - half_period);
        };
    }; -- drive_clock()
    
    -- If enabled, then the clock generator should start at time zero
    -- and not be affected by reset (which is why this code is in the
    -- agent not the BFM - the BFM gets rerun() during a reset, whereas
    -- the agent does not).
    run() is also {
        if tx_clock_period > 0 {
            start drive_clock();
        };
    }; -- run()

}; -- extend ACTIVE has_tx_path xserial_agent_u

'>



 Configuration

<'
extend xserial_agent_u {
    
    // configure
    configure(ctr : uint, new_params : xserial_agent_config_params) is {
        config.params = new_params.copy();
    }; -- configure
};

'>

