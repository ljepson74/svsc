/*------------------------------------------------------------------------- 
File name   : xserial_collector.e
Title       : XSerial collector unit
Project     : XSerial eVC
Created     : 2008
Description : This file contains the private sections of the collector.
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
extend xserial_collector_u {
    tf_testflow_unit;
    keep soft tf_domain == XSERIAL_TF;
    event tf_phase_clock is only @unqualified_clock_rise;

    -- These are the qualified clock events for this direction
    event clock_rise is only
      true(not get_enclosing_unit(xserial_agent_u).reset_asserted) @unqualified_clock_rise;
    event clock_fall is only
        true(not get_enclosing_unit(xserial_agent_u).reset_asserted) @unqualified_clock_fall;

    -- This method waits until a new frame start bit is detected. It returns
    -- the number of clock cycles it waited for the start bit to be detected
    private wait_frame_start() : uint @tf_phase_clock is {
        while sig_data$ == 1 {
            wait cycle;
            result += 1;
        };
    }; -- wait_frame_start()
    

    -- This method should be passed an instance of a xserial_frame_s. It
    -- collects a frame from the interface and unpacks it into the frame
    -- struct. This method should be called immediately after the
    -- wait_frame_start() method has detected a start bit. If
    -- has_protocol_checker is TRUE, then a DUT error will be reported if
    -- there is any error in the frame format.

    private collect_a_frame() @tf_phase_clock is {
        monitor_frame = new MONITOR xserial_frame_s;

        -- wait until ready for a frame
        monitor_frame.inter_frame_delay = wait_frame_start();
        emit frame_started_eo$;
        message(MEDIUM, direction, " Collector detected frame start");
        msg_started(HIGH, append(direction, " Collecting frame"), 
                    monitor_frame);
        frame_started_o$.write(monitor_frame);

        -- collect the frame
        -- Raw data is collected in this variable
        var raw_bits : list of bit;
        
        -- Collect the raw data
        for i from 1 to 14 {
            raw_bits.add(sig_data$);
            wait cycle;
        };
        raw_bits.add(sig_data$);
        
        -- Unpack the raw data into the frame struct and check it's
        -- format if required.
        monitor_frame.unpack_frame(raw_bits, has_protocol_checker);
        
        message(MEDIUM, direction, " Collector detected frame end");
        msg_ended(HIGH, append(direction, " Collecting frame"), 
                  monitor_frame);

        emit frame_ended_eo$;
        
        -- Pass to upper components
        frame_ended_o$.write(monitor_frame);
    };
    
    -- This method continually monitors frames at the interface of
    -- this agent
    
    private collect_frames() @tf_phase_clock is {
        message(LOW, direction, " collect_frames started");
        while TRUE {
            // Collect a frame:
            collect_a_frame();
        };
    };

    
   -- This TCM starts the monitor. It gets called by the agent to start the
    -- monitor at the start of the test and each time reset is asserted. The
    -- user can delay activation of the monitor by extending this method
    -- using 'is first'.
    tf_main_test() @tf_phase_clock is also {
        -- Start the main monitor.
        start collect_frames();
        // Register the thread as running until POST_TEST, non blocking
        tf_get_domain_mgr().register_thread_by_name(me, "collect_frames", 
                                                    POST_TEST, FALSE);
     }; -- tf_main_test()
    
    // Attributes that are calculated (and just that sampling of fields)
    tr_get_attribute_value(inst: any_struct, name: string): string is also {
        if inst is a xserial_frame_s (f) then {
            result = f.get_attribute_value(name);
        };
    };
}; -- extend xserial_collector_u 
'>
