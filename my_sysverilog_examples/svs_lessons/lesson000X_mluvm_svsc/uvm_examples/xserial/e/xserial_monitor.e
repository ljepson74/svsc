/*------------------------------------------------------------------------- 
File name   : xserial_monitor.e
Title       : XSerial monitor unit
Project     : XSerial eVC
Created     : 2008
Description : This file contains the private sections of the monitor.
Notes       : The collector collects all activity on the bus and collects
            : information on each frame that occurs.
            : It passes the collected info, after basic processing, to the
            : monitor.
            : The monitor performs higher level process, coverage and checks 
--------------------------------------------------------------------------- 
Copyright (c) 2008 - 2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
-------------------------------------------------------------------------*/ 

<'

package cdn_xserial;

-- Add a logging method to the MONITOR frame.
extend MONITOR xserial_frame_s {

    -- This method returns a log file line for this frame.
    package log_frame(direction : xserial_direction_t) : string is {
        result = appendf("%8d%9d   %-11.11s %s  %s", 
                         sys.time, inter_frame_delay, name, 
                         direction, nice_string());
    }; -- log_frame()

}; -- extend MONITOR xserial_frame_s

-- Add internal stuff to monitor unit
extend xserial_monitor_u {
    tf_testflow_unit;
    keep soft tf_domain == XSERIAL_TF;
    event tf_phase_clock is only @unqualified_clock_rise;
    
    -- These are the qualified clock events for this direction
    event clock_fall is @collector.clock_fall;
    
    -- This method writes a header to the log file with information 
    -- about what is contained in each column of the log file along with
    -- the date and time the file was created.
    private write_log_header() is {
        -- Write date and time, filename etc. along with field headings to
        -- log file.
        message(XSERIAL_FILE, LOW, 
                append(append(file_logger.to_file, ".elog"), 
                       " - created ", date_time()));
        message(XSERIAL_FILE, LOW, "");
        message(XSERIAL_FILE, LOW, 
                "    TIME    DELAY   ENV         DIR DEST   ",
                "PAYLOAD        STATUS");
        message(XSERIAL_FILE, LOW,
                "    ****    *****   ***         *** ****   ",
                "*******        ******");
        message(XSERIAL_FILE, LOW, "");
    }; -- write_log_header()

    -- This field is used to ensure that the log file header is not
    -- rewritten if reset is reapplied during the test.
    private log_header_written : bool;
        keep log_header_written == FALSE;
    
    -- If this is the beginning of the test, write a file log header. The
    -- log_header_written field is used to prevent the log header being
    -- written again if rerun() is called.
    tf_env_setup()@tf_phase_clock is also {
        write_log_header();
    };
    
    tf_main_test() @tf_phase_clock is also {
        -- Spec says that we should always come out of reset assuming that
        -- remote device is ready to receive data.
        ready = TRUE; 
    };
    
    
    // Implement the started and ended ports
    //
    
    started_write(frame :  MONITOR xserial_frame_s) is also { 
        monitor_frame = frame;
        msg_started(MEDIUM, append(direction, " Monitoring frame"), 
                    monitor_frame);
    };
    

    
    ended_write(frame :  MONITOR xserial_frame_s) is also {
        
        -- Analysis the frame, and udpate its fields accordingly
        frame.name = agent.name;

        if frame.payload is a HALT MESSAGE xserial_frame_payload_s {
            ready = FALSE;
        };

        if frame.payload is a RESUME MESSAGE xserial_frame_payload_s {
            ready = TRUE;
        };

        emit frame_ended;
        num_frames += 1;
        message(XSERIAL_FILE, MEDIUM,
                    monitor_frame.log_frame(direction));
        message(HIGH, direction, " Monitor detected frame end: ", 
                monitor_frame);
                
        msg_ended(MEDIUM, append(direction, " Monitoring frame"), 
                  monitor_frame);
        -- pass to upper components
        frame_ended_o$.write(monitor_frame);
 
        if direction == TX {
            agent.tx_frame = monitor_frame;
            emit agent.tx_frame_done;
            
        } else {
            agent.rx_frame = monitor_frame;
            emit agent.rx_frame_done;
        };
    }; // ended_write()


    
    -- This method returns a string that indicates context. It is used
    -- during error reporting.
    package error_header() : string is {
        result = append(direction, " Monitor");
    }; -- err_header()

    -- This method reports the current status of the monitor.    
    show_status() is {
        message(LOW, direction, " Monitor detected ", dec(num_frames), 
                " frames");
    }; -- show_status()



    
    // Calculate recoreded attributes 
    tr_get_attribute_value(inst: any_struct, name: string): string is also {
        if inst is a xserial_frame_s (f) then {
            result = f.get_attribute_value(name);
        };
    };


}; -- extend xserial_monitor_u 

'>

