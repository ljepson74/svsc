/*------------------------------------------------------------------------- 
File name   : xserial_bfm_h.e
Title       : XSerial BFM public interface
Project     : XSerial eVC
Created     : 2008
Description : This file declares the public interface of the BFM unit. 
Notes       : There is no RX BFM because the RX link direction contains no
            : signals that the eVC can drive. As such, the entire RX path
            : functionality is contained in the RX monitor and the eVC does
            : not need either an RX BFM or an RX sequence driver.
            :
            : The BFM depends on the functionality of the RX and TX
            : monitors.
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
-------------------------------------------------------------------------*/ 

<'

package cdn_xserial;


-- This unit is the BFM used for the transmit direction (i.e. sending data
-- from the eVC to the DUT).
unit xserial_bfm_u like uvm_bfm {
    tf_testflow_unit;
    event tf_phase_clock is only @tx_monitor.unqualified_clock_rise;
   
    -- This field is a pointer to the TX monitor.
    tx_monitor : xserial_monitor_u;
    
    -- This field is a pointer to the RX monitor (or NULL if the RX path is
    -- disabled).
    rx_monitor : xserial_monitor_u;
        keep soft rx_monitor == NULL;

    -- This field is a pointer to the sequence driver.
    driver : xserial_driver_u;
    
    -- This field holds the signal name of the TX_CLOCK signal on the
    -- XSERIAL interface.
    sig_tx_clock : out simple_port of bit is instance;

    -- This field holds the signal name of the TX_DATA signal on the XSERIAL
    -- interface.
    sig_tx_data  : out simple_port of bit is instance;
   
}; -- unit xserial_bfm_u


'>


