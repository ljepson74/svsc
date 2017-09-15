/*------------------------------------------------------------------------- 
File name   : xcore_monitor.e
Title       : Monitor for XCore eVC
Project     : XCore eVC
Created     : 2008
Description : This file sets up the monitor infrastructure for the eVC
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide.

-------------------------------------------------------------------------*/ 

<'

package cdn_xcore;

unit xcore_monitor_u like uvm_monitor {    
    -- This field specifies whether to perform data and protocol checks
    has_checks : bool;

    -- This field specifies whether to collect coverage
    has_coverage : bool;

    !xbus_agent_monitor  : xbus_agent_monitor_u;
    !xserial_rx_monitor  : xserial_monitor_u;
    !xserial_tx_monitor  : xserial_monitor_u;

   
    -- Shadow registers
    !reg_file : XCORE vr_ad_reg_file;
    
    -- Info from the XSerial monitor:
    !cur_tx_frame : MONITOR xserial_frame_s;
    !cur_rx_frame : MONITOR xserial_frame_s;
   
    -- This event is emited when an RX frame (sent to DUT) is seen on line
    event rx_frame_started;

    -- This event is emited when a TX frame (transmited by DUT) is seen on line
    event tx_frame_started;

    -- This event is emited when an RX frame (sent to DUT) is done
    event rx_frame_ended;

    -- This event is emited when a TX frame (transmited by DUT) is done
    event tx_frame_ended;

    -- In ports for getting Xserial information
    -- Start of frames
    xserial_tx_frame_started_ei : in event_port is instance;
    xserial_rx_frame_started_ei : in event_port is instance;
    

    connect_ports() is also {
        do_bind(xserial_tx_frame_started_ei, 
                xserial_rx_monitor.frame_started_eo);
        do_bind(xserial_rx_frame_started_ei, 
                xserial_tx_monitor.frame_started_eo);
    };
    
    -- End of frames
    -- In ports - getting frames from i/f monitor
    xserial_tx_frame_ended_i : in interface_port of tlm_analysis of
                                           MONITOR xserial_frame_s 
                                           using prefix=tx_ is instance;
    xserial_rx_frame_ended_i : in interface_port of tlm_analysis of
                                           MONITOR xserial_frame_s 
                                           using prefix=rx_ is instance;
    
    xserial_tx_frame_ended_o : out interface_port of tlm_analysis of
                                           MONITOR xserial_frame_s is instance;
    xserial_rx_frame_ended_o : out interface_port of tlm_analysis of
                                           MONITOR xserial_frame_s is instance;
    
    -- Out ports - passing frames to upper level/s
    -- These are xserial-frames written to the device (for it to transmit),
    -- and xserial-frames read from the device, after it received them from the 
    -- eVC agent
    tx_frame_written_o : out interface_port of tlm_analysis of
                                           MONITOR xserial_frame_s is instance;
    rx_frame_read_o    : out interface_port of tlm_analysis of
                                           MONITOR xserial_frame_s is instance;
    
    -- By default - bind to empty. To be bound later
    keep bind(tx_frame_written_o, empty);
    keep bind(rx_frame_read_o, empty);

    // implement the two tlm_analysis ports
    tx_write(frame : MONITOR xserial_frame_s) is {
        cur_tx_frame = frame;
        xserial_tx_frame_ended_o$.write(frame);
        emit tx_frame_ended;
    };
    rx_write(frame : MONITOR xserial_frame_s) is {
        cur_rx_frame = frame;
        xserial_rx_frame_ended_o$.write(frame);
        emit rx_frame_ended;
    };
  
    connect_ports() is also {
        xserial_rx_monitor.frame_ended_o.connect(
                xserial_tx_frame_ended_i);
        xserial_tx_monitor.frame_ended_o.connect(
                xserial_rx_frame_ended_i);
    };

    
    -- Info from the XBus monitor:
   
    !cur_xbus_transfer : MONITOR xbus_trans_s;

    -- An in TLM port for getting XBus transfers
    xbus_transfer_ended : in  interface_port of tlm_analysis of
                                          MONITOR xbus_trans_s 
                                          using prefix=xbus_ is instance;
    
    // Implement the in port
    xbus_write(transfer : MONITOR xbus_trans_s ) is {
        cur_xbus_transfer = transfer;
    };

    connect_ports() is also {
        do_bind(xbus_transfer_ended,
                xbus_agent_monitor.transfer_ended_o);
    };
    

    event reset_deassert;

    -- This is sampled from the base_addr signal (as specified in the
    -- sig_base_addr field in the env) at the deassertion of reset and 
    -- gives the XBus base address the XCore module is configured to 
    -- respond to.
    !base_address : uint(bits:16);

    -- This port must be bound to the base_addr signal of the XCore module. 
    -- The eVC samples this signal at the de-assertion of reset to determine
    -- what addresses the XCore module will respond to.
    sig_base_addr :  in simple_port of bit is instance;

    -- This port must be bound to the reset signal of the XCore module.
    sig_reset : in simple_port of bit is instance;   

    -- This port must be bound to the flow signal of the XCore module.
    sig_flow : in simple_port of bit is instance;   

    -- This port must be bound to the halt_int signalof the XCore module.
    sig_halt_int : in simple_port of bit is instance;    

   
    -- This port must be bound to the item_count signal of the XCore module.
    sig_item_count : in simple_port of bit is instance;     

};

extend xcore_monitor_u {
    

    -- This event is emitted at the deassertion of reset.
    event reset_deassert is only fall(sig_reset$) @sim;
   

    -- As reset is deasserted, sample the base_address from the HDL.    
    on reset_deassert {
        base_address = (sig_base_addr$).as_a(uint(bits:16)) * 0x100;
    };

}; -- unit xcore_monitor_u


'>

