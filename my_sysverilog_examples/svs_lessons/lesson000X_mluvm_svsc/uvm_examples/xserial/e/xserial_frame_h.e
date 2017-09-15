/*------------------------------------------------------------------------- 
File name   : xserial_frame_h.e
Title       : XSerial eVC frame structure
Project     : XSerial eVC
Created     : 2008
Description : This file declares the format of the XSerial frame.
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
-------------------------------------------------------------------------*/ 

<'

package cdn_xserial;

-- This type is used to enumerate the possible kinds of frame. The default
-- is a GENERIC frame that contains only the information relating directly
-- to the frame. MONITOR frames are used by the monitor to hold a frame with
-- certain additional fields and methods relating to monitoring. The TX
-- sequence driver uses instances of TX frames that contain additional
-- information about which agent generated them etc.
type xserial_frame_kind_t : [GENERIC, MONITOR, TX];


-- In addition to the errors that can occur in the payload, the following
-- errors can occur in the main part of the frame.
extend xserial_frame_status_t : [BAD_START,  -- start bit is not 0
                                    BAD_PARITY, -- parity bit is incorrect
                                    BAD_STOP];  -- stop bit is not 1
                                    
              
              
-- This struct represents a single frame. It is used as the sequence
-- item for the transmit sequence interface.                      
struct xserial_frame_s like any_sequence_item {

    -- For generated frames, this field is automatically updated by the eVC
    -- during post_generate() to indicate what error conditions are
    -- present in the frame. The user should not attempt to constrain or
    -- assign a value to this field. When a frame is unpacked, this field
    -- reflects the result of the unpacking. If this field is an empty
    -- list then no errors are present in the frame.
    !status : list of xserial_frame_status_t;

    -- This field determines what kind of frame this is.
    kind : xserial_frame_kind_t;
        keep soft kind == GENERIC;

    -- This field is the physical start bit of the frame and, by default, is
    -- always 0 (the legal value). To create an erroneous start bit, 
    -- constrain this field to be 1.
    %start_bit : bit;
        keep soft start_bit == 0;
        
    -- This field holds the payload part of the frame. See the file
    -- xserial_frame_payload_h.e for more details.
    %payload : xserial_frame_payload_s;
    
    -- For generated frames, this field controls whether the parity bit is
    -- correct or bad. By default, correct parity is generated. For unpacked
    -- frames, this field indicates whether the unpacked parity bit is
    -- correct or not.
    bad_parity : bool;
        keep soft bad_parity == FALSE;
    
    -- This field contains the parity bit for the frame. Parity is
    -- calculated as the even parity of all data bits in the payload. The
    -- virtual field parity_kind can be used to constrain either correct
    -- or incorrect parity values in this field.
    %parity : bit;
        keep not read_only(bad_parity) => parity == calc_parity();
        keep     read_only(bad_parity) => parity != calc_parity();
        
    -- This field is the physical stop bit of the frame and, by default, is
    -- always 1 (the legal value). To create an erroneous stop bit,
    -- constrain this field to be 0.
    %stop_bit : bit;
        keep soft stop_bit == 1;
        
    -- This method returns the even parity of a payload.
    calc_parity() : bit is {
        for each (b) in payload.pack_payload() {
            result ^= b;
        };
    }; -- calc_parity()
    
    -- This method returns TRUE if the parity field contains the correct
    -- even parity for the payload. This can be used on received frames to
    -- quickly determine the status of the parity bit.
    parity_ok() : bool is {
        result = (parity == calc_parity());
    }; -- parity_ok()
    
    post_generate() is also {
        update_status();
    }; -- post_generate()
    
    -- This method returns the frame as a list of bits. By using this method
    -- rather than explicitly packing the struct, the user does not need
    -- to be aware of the details of how a frame is packed. Note that in
    -- the XSerial eVC example, this is relatively trivial, but in more 
    -- complex eVCs, the process of packing a struct may be complex.
    pack_frame() : list of bit is {
        result = pack(packing.low, start_bit, payload.pack_payload(),
                      parity, stop_bit);
    }; -- pack_frame()
    
    -- This method takes a bitstream and unpacks it into the frame struct.
    -- As with pack_frame(), this method hides the implementation details
    -- of the struct packing/unpacking from the user. In addition, if the
    -- check_protocol field is TRUE, then this method checks the protocol
    -- of the bitstream and reports dut errors where the protocol is
    -- illegal.
    unpack_frame(bitstream : list of bit, check_protocol : bool) is {

        unpack_frame_internal(bitstream, check_protocol);
        update_status();

    }; -- unpack_frame()

    -- The unpack_frame() method calls the unpack_frame_internal() method
    -- and then calls update_status(). This allows sub-types of the frame to
    -- extend the unpacking behaviour while still ensuring that
    -- update_status() gets called last.
    unpack_frame_internal(bitstream : list of bit,
                          check_protocol : bool) is {

        -- The frame should always be exactly 15 bits long.
        if bitstream.size() != 15 {
            error("FATAL: Frame is not 15 bits long");
        };
        
        -- Unpack the start bit
        unpack(packing.low, bitstream, start_bit);
        
        -- Check that the start bit is legal
        if check_protocol {
            check start_bit_err that start_bit == 0
                else dut_error("Frame start bit is not 0");
        };
        
        -- Unpack the payload
        payload = new;
        payload.unpack_payload(bitstream[1..12], check_protocol);
        
        -- Unpack the parity and stop bits;
        unpack(packing.low, bitstream[13..14], parity, stop_bit);

        -- Check the parity bit
        if check_protocol {
            check parity_err that parity_ok()
                else dut_error("Frame has bad parity: ", parity);
        };
        
        -- Check the stop bit.
        if check_protocol {
            check stop_bit_err that stop_bit == 1
                else dut_error("Frame stop bit is not 1");
        };
        
    }; -- unpack_frame_internal()
    
    -- This method returns a convenient string representation of the
    -- contents of the frame. This is used for logging, waveform viewing, 
    -- etc.
    nice_string(): string is also {
        result = append(payload.nice_string(), " ERRORS:");
        if status.size() == 0 {
            result = append(result, "NONE");
        } else {
            for each in status {
                result = append(result, it);
                if index < (status.size()-1) {
                    result = append(result, ",");
                };
            };
        }
    }; -- nice_string()
    
    -- This method compares this frame with a frame supplied as a parameter.
    -- If the compare_dest field is false, then differences in the payload
    -- destination fields are ignored. It returns a list of strings that
    -- contains all detected differences.
    compare_frames(exp_frame : xserial_frame_s, 
                   compare_dest : bool) : list of string is {
        if exp_frame.start_bit != start_bit {
            result.add(append("Expected start bit: ", 
                              exp_frame.start_bit,
                              ", Actual start bit: ", 
                              start_bit));
            return result;
        };
        result.add(payload.compare_payloads(exp_frame.payload,
                                            compare_dest));
        if (BAD_PARITY in status) != (BAD_PARITY in exp_frame.status) {
            result.add(append("Expected parity status:",
                              exp_frame.parity_ok()?"OK":"BAD",
                              ", Actual parity status:",
                              parity_ok()?"OK":"BAD"));
        };
        if exp_frame.stop_bit != stop_bit {
            result.add(append("Expected stop bit: ", 
                              exp_frame.stop_bit,
                              ", Actual stop bit: ", 
                              stop_bit));
        };
    }; -- compare_frames()
    
    -- This method is called in post_generate() and also in unpack_frame()
    -- to update the status field according to the detected errors in the
    -- frame.
    update_status() is {

        -- Assume that this payload is going to be legal until we discover
        -- otherwise.
        status = {};

        -- If the start bit is illegal, then reflect this in 
        -- the status  field
        if start_bit != 0 {
            status.add(BAD_START);
        };
        
        -- If there are any protocol errors in the payload, then reflect 
        -- these in the status field.
        status.add(payload.status);
        
        -- If the parity is bad then reflect this in the status field.
        if not parity_ok() {
            status.add(BAD_PARITY);
            bad_parity = TRUE;
        } else {
            bad_parity = FALSE;
        };            
            
        -- If the stop bit is illegal, then reflect this in the status field
        if stop_bit != 1 {
            status.add(BAD_STOP);
        };
        
    }; -- update_status()

    
    -- Called by Structured Messages 
    get_attribute_value(name: string): string is {
     
        if name == "destination" or 
           name == "data" {
            
            if payload == NULL {
                return "";
            };
            result = payload.get_attribute_value(name);
        };
        
    };
    
}; -- struct xserial_frame_s



'>

