/*------------------------------------------------------------------------- 
File name   : xserial_monitor_h.e
Title       : XSerial monitor unit public interface
Project     : XSerial eVC
Created     : 2008
Description : The monitor unit implements a monitor for one direction of
            : traffic on an XSerial interface. This file defines the public
            : interface of the monitor unit. One instance of the monitor
            : unit is placed in the agent for each data direction. The
            : monitor is largely self-contained and stand-alone. It creates
            : instances of the MONITOR sub-type of the frame (which
            : contains additional information to the GENERIC sub-type) and
            : optionally writes information to a log file.
            : The monitor gets frames that are collected by the collector,
            : analyzes them, adds to the logs, and performs checks and 
            : coverage
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
-------------------------------------------------------------------------*/ 

<'

package cdn_xserial; 



-- Provide a message tag that can be used to direct certain message
-- actions to a log file.
extend message_tag: [XSERIAL_FILE];


-- This unit contains a monitor that is capable of monitoring traffic in 
-- one direction on an XSerial link. Two instances of this unit are 
-- required to monitor a bidirectional link.
unit xserial_monitor_u like uvm_monitor {

    collector : xserial_collector_u is instance;
      keep collector.direction == value(direction);
      keep collector.has_protocol_checker == value(has_protocol_checker);

    -- This field indicates whether the monitor is monitoring the TX or RX
    -- direction.
    direction : xserial_direction_t;

    -- This field controls whether the monitor should collect 
    -- coverage information
    has_coverage : bool;

    -- This is the logger used for creating log files.
    file_logger : message_logger is instance;    
        keep file_logger.tags == {XSERIAL_FILE};
        keep soft file_logger.to_screen == FALSE;
        keep soft file_logger.format == none;
        keep soft file_logger.verbosity == FULL;

    
    -- If this field is TRUE then the agent does protocol checking
    has_protocol_checker : bool;

    
    -- This field is a pointer to the monitor for the reverse link 
    -- direction. If such a monitor does not exist (perhaps one link 
    -- direction has been disabled), then this field will be NULL.
    !reverse_monitor : xserial_monitor_u;
    
    -- This field indicates whether the device sending the frames that this
    -- monitor is monitoring is currently ready to receive frames or not.
    !ready : bool;
     
    -- The monitored frame is built up in this field.
    !monitor_frame : MONITOR xserial_frame_s;
    
    -- This field counts the number of frames this monitor detects over the
    -- duration of the test.
    num_frames : uint;
        keep num_frames == 0;
    
    -- Getting infomration from the collector
    frame_started_ei : in event_port is instance;
        keep bind (frame_started_ei, collector.frame_started_eo);
        
    frame_ended_ei : in event_port is instance;
        keep bind (frame_ended_ei, collector.frame_ended_eo);

    -- This event is emitted at the start of a frame.
    event frame_started is @frame_started_ei$;
    
    -- This event is emitted at the end of a frame.
    event frame_ended is @frame_ended_ei$;

    
    -- These ports get collected frames from the collector
    frame_started_i : in interface_port of tlm_analysis
                                        of MONITOR xserial_frame_s
                                        using prefix=started_
                                        is instance;
        keep bind (frame_started_i, collector.frame_started_o);
    
    started_write(frame :  MONITOR xserial_frame_s) is { };

    frame_ended_i : in interface_port of tlm_analysis
                                          of MONITOR xserial_frame_s
                                          using prefix=ended_
                                          is instance;
        keep bind (frame_ended_i, collector.frame_ended_o);
    ended_write(frame :  MONITOR xserial_frame_s) is { };
   

    -- This port passes collected frames to upper components
    -- By default - bound to empty.
    frame_ended_o : out interface_port of tlm_analysis of MONITOR 
                                           xserial_frame_s is instance;
        keep bind (frame_ended_o, empty);
    
    
    -- Passing events to upper components
    frame_started_eo : out event_port is instance;
        keep bind (frame_started_eo, empty);
    on frame_started { emit frame_started_eo$;};

    
    event clock_rise is cycle @collector.clock_rise;
    event unqualified_clock_rise is cycle @collector.unqualified_clock_rise;
}; -- extend  xserial_monitor_u

'>


