/*------------------------------------------------------------------------- 
File name   : xserial_frame_payload_message_h.e
Title       : XSerial eVC frame payload structure for message frame
Project     : XSerial eVC
Created     : 2008
Description : This file declares the format of the MESSAGE subtype of the
            : XSerial frame payload. 
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
-------------------------------------------------------------------------*/ 

<'

package cdn_xserial;

-- Extend the frame format type to provide a new format called MESSAGE.
extend xserial_frame_format_t : [MESSAGE = 2'b01];


-- This type enumerates the possible messages that can be sent in a MESSAGE
-- frame.
type xserial_frame_message_t : [UNDEFINED =  UNDEF,
                                   IDLE   = 8'x00,
                                   HALT   = 8'x01,
                                   RESUME = 8'x02];


-- A MESSAGE frame can potentially have an illegal message in it, so extend
-- the frame status type to cover this error condition.
extend xserial_frame_status_t : [BAD_MESSAGE];


-- Now extend the MESSAGE sub-type of the payload.
extend MESSAGE xserial_frame_payload_s {

    -- This field contains the message for MESSAGE frames. At present the
    -- following values are defined, although users can add further messages
    -- by extending the xserial_frame_message_t type:
    --   IDLE - has no effect - can be used for testing messaging
    --   HALT - indicates to remote end of link that local end cannot
    --          currently receive any more data 
    --          (e.g. because a FIFO is full).
    --   RESUME - indicates to remote end of link that previous
    --            HALT condition is cancelled.
    -- To create illegal messages, this field should be constrained to
    -- UNDEFINED. By default, this field is constrained not to be UNDEFINED.
    frame_message : xserial_frame_message_t;
        keep soft frame_message != UNDEFINED;

    %physical_message : byte;
        keep (read_only(frame_message) != UNDEFINED) =>
            physical_message == read_only(frame_message).as_a(uint);
        keep (read_only(frame_message) == UNDEFINED) =>
            physical_message not in
                all_values(xserial_frame_message_t).all(it != UNDEFINED).
                       apply(it.as_a(uint));
    
    -- Unpack the message part of a MESSAGE payload
    unpack_payload_internal(bitstream      : list of bit, 
                            check_protocol : bool) is also {
    
        --unpack the frame_message from the bitstream.
        unpack(packing.low, bitstream[4..11], physical_message);
        if physical_message in all_values(xserial_frame_message_t).
                    apply(it.as_a(uint)) {
            frame_message = physical_message.as_a(xserial_frame_message_t);
        } else {
            frame_message = UNDEFINED;
        };
        
        -- Make sure we've got a legal message. We'll assume that if
        -- the user extends xserial_frame_message_t then this makes the
        -- new value a legal message.
        if check_protocol {
            check illegal_frame_msg that frame_message != UNDEFINED
                else dut_error("Illegal frame_message in MESSAGE frame: ", 
                                physical_message);
        };
        
    }; -- unpack_payload_internal()
   
    -- Add the message value to the 'nice string'.
    nice_string(): string is also {
        result = appendf("%s MESSAGE:%-6s", result, frame_message);
    }; -- nice_string()
   
    -- Compare messages
    compare_payloads(exp_payload : xserial_frame_payload_s, 
                     compare_dest : bool) : list of string is also {
        if exp_payload is a MESSAGE xserial_frame_payload_s (m) and
           m.frame_message != frame_message {
            result.add(append("Expected message: ", 
                              m.frame_message,
                              ", Actual message: ", 
                              frame_message));
        };
    }; -- compare_payloads()

    update_status() is also {

        -- If the message is illegal, make sure the status field reflects
        -- this.
        if frame_message == UNDEFINED {
            status.add(BAD_MESSAGE);
        };

    }; -- update_status()

}; -- extend MESSAGE xserial_frame_payload_s

'>

