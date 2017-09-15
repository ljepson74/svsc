/*------------------------------------------------------------------------- 
File name   : xserial_collector_h.e
Title       : XSerial collector unit
Project     : XSerial eVC
Created     : 2008
Description : This file defines the collector.
Notes       : The collector collects all activity on the bus and collects
            : information on each frame that occurs.
            : It passes the collected info, after basic processing, to the
            : monitor.
            : The monitor performs higher level process, coverage and checks 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
-------------------------------------------------------------------------*/ 

<'
package cdn_xserial;
'>

<'

-- Provide a MONITOR frame sub-type with some extra fields and methods to
-- assist in monitoring.
extend MONITOR xserial_frame_s {

    -- This field indicates which eVC instance this frame is 
    -- associated with.
    name : xserial_env_name_t;
    
    -- This field holds the time between the end of the previous frame and
    -- the beginning of this one.
    inter_frame_delay : uint;

}; -- extend MONITOR xserial_frame_s


unit xserial_collector_u like uvm_collector {
    -- This field indicates whether the collector is monitoring the TX or RX
    -- direction.
    direction : xserial_direction_t;

    frame_started_eo : out event_port is instance;
    frame_ended_eo   : out event_port is instance;
    
    -- These ports pass collected frames to upper components
    -- By default - bound to empty.
    frame_started_o : out interface_port of tlm_analysis 
                                         of MONITOR xserial_frame_s
                                         is instance;
        keep bind (frame_started_o, empty);
    
    frame_ended_o : out interface_port of tlm_analysis 
                                           of MONITOR xserial_frame_s
                                           is instance;
        keep bind (frame_ended_o, empty);

    -- If this field is TRUE then the agent does protocol checking
    has_protocol_checker : bool;

    -- This is the clock signal of the link being monitored.
    sig_clock : in simple_port of bit is instance;
    
    -- This is the data signal of the link being monitored.
    sig_data : in simple_port of bit is instance;

    -- This is the main clock rise event for this direction. Note that this
    -- clock is qualified with reset and so is only emitted when reset is
    -- not asserted.
    event clock_rise;

    -- This is the main clock fall event for this direction. Note that this
    -- clock is qualified with reset and so is only emitted when reset is
    -- not asserted.
    event clock_fall;

    -- The monitored frame is built up in this field.
    !monitor_frame : MONITOR xserial_frame_s;
       
     -- Clocks

    -- This event is the clock change event, the base of the
    -- rise/fall clocks 
    event unqualified_clock_change is change(sig_clock$) @sim;

    -- This event is the clock rise event for this direction prior to 
    -- qualification with reset.
    event unqualified_clock_rise;

    -- This event is the clock fall event for this direction prior to 
    -- qualification with reset.
    event unqualified_clock_fall;
    
    on unqualified_clock_change {
       if (sig_clock$ == 0) then {
          emit unqualified_clock_fall;
       } else {
          emit unqualified_clock_rise;
       };
    }; -- on unqualified_clock_change
}; // unit xserial_collector_u


'>
