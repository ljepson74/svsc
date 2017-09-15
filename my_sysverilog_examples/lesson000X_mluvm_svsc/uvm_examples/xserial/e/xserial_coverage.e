/*------------------------------------------------------------------------- 
File name   : xserial_coverage_h.e
Title       : Coverage definitions
Project     : XSerial eVC
Created     : 2008
Description : This file provides a basic functional coverage model for
            : frames. The user can extend this to create additional
            : coverage as required.
Notes       : Two different coverage events are used here because, at
            : present, Specman only supports one-dimensional per-instance
            : coverage. In this case, we have two dimensions: the agent
            : name and the direction. By using two events, one for each
            : direction, separate coverage groups can be maintained for
            : each direction.
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
-------------------------------------------------------------------------*/ 

<'

package cdn_xserial;


extend xserial_frame_s {

    -- This event is emitted by the appropriate TX monitor whenever a frame
    -- transmission completes. It is used to collect coverage.
    event tx_frame_done;
    
    -- This event is emitted by the appropriate RX monitor whenever a frame
    -- reception completes. It is used to collect coverage.
    event rx_frame_done;
    
}; -- extend xserial_frame_s


extend has_coverage xserial_monitor_u {
    
    -- Each time a frame ends, emit the event used to collect coverage for
    -- that frame.
    on frame_ended {
        case direction {
            TX : { emit monitor_frame.tx_frame_done; };
            RX : { emit monitor_frame.rx_frame_done; };
        };
    };

}; -- extend xserial_monitor_u


extend MONITOR xserial_frame_s {

    // Note the use of per_unit_instance.
    // For seeing the coverage report of only one agent, use
    // the cover name or e_path in the command. For example:
    // show cover xserial_frame_s.tx_frame_done(XSERIAL_A)
    cover tx_frame_done using 
                          per_unit_instance = xserial_agent_u is {
        item destination : uint(bits:2) = payload.destination;
        item frame_format : xserial_frame_format_t = 
          payload.frame_format;
        item data : byte = 
          payload.as_a(DATA xserial_frame_payload_s).data
          using when = (payload is a DATA xserial_frame_payload_s);
        item frame_message : xserial_frame_message_t = 
          payload.as_a(MESSAGE xserial_frame_payload_s).frame_message
          using when = (payload is a MESSAGE xserial_frame_payload_s);
        item parity;
        item inter_frame_delay;
    }; -- cover tx_frame_done
        
    cover rx_frame_done using 
                          per_unit_instance=xserial_agent_u is {
        item destination : uint(bits:2) = payload.destination;
        item frame_format : xserial_frame_format_t = 
          payload.frame_format;
        item data : byte = 
          payload.as_a(DATA xserial_frame_payload_s).data
          using when = (payload is a DATA xserial_frame_payload_s);
        item frame_message : xserial_frame_message_t = 
          payload.as_a(MESSAGE xserial_frame_payload_s).frame_message
          using when = (payload is a MESSAGE xserial_frame_payload_s);
        item parity;
        item inter_frame_delay;
    }; -- cover rx_frame_done
        
}; -- extend xserial_frame_s

'>

